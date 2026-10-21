#!/usr/bin/env python3
"""Build the /tenders section of deadlinebiddesk.com from the SA eTenders OCDS API.

Runs unattended from .github/workflows/refresh-tenders.yml once a day.
Python 3.12, standard library only. No secrets, no accounts.

    python build_site.py --today 2026-10-12            # fetch + build (+ IndexNow ping)
    python build_site.py --today 2026-10-12 --no-ping  # build only
    python build_site.py --ping-file changed.txt       # ping IndexNow only

What it writes (all under the repo root, i.e. this file's directory):

    tenders/index.html                       overview
    tenders/closing-this-week.html           closing today .. today+6
    tenders/province/<slug>[-N].html         one hub per province present
    tenders/category/<slug>[-N].html         one hub per category present
    tenders/t/<ocid>.html                    one page per OPEN tender
    tenders/closed.html                      note for closed / removed tenders
    sitemap.xml                              /tenders pages + indexable site pages
    robots.txt                               existing rules kept, Sitemap: line added

Everything under tenders/ is owned by this script: files it did not write on
this run are deleted (that is how closed tenders disappear).

Safety: all fetching and rendering happens in memory first. If the API fails
badly (too few tenders, request budget blown, open count collapses compared
with the previous run) the script exits non-zero before touching any file.

eTenders OCDS API quirks handled here (see also pipeline/fetch_sa.py):
  * dateFrom/dateTo filter on the release (advertise) date, not closing date,
    so we walk one-day windows back ~60 days and filter on closing date.
  * Ragged pages: a page can be short and still have more behind it. Only an
    empty page at PageSize=100 is treated as the end of a window.
  * PageSize=500 returns non-JSON; we use 100.
  * Some individual releases are "poison": any page that contains them returns
    HTTP 500, deterministically. A failing PageSize=100 page is re-fetched as
    ten PageSize=10 pages covering the same offsets, and a failing size-10 page
    as ten PageSize=1 pages, so only the poison records themselves are lost.
  * Sporadic 5xx and connection timeouts: retried with backoff.
  * Since late 2026 the releases no longer carry tender.province,
    tender.category, tender.briefingSession or tender.status. They are used
    when present; otherwise the province is only shown when the buyer's own
    name states it (marked as such), and nothing else is guessed.

Determinism: the reference date comes from --today (the Action passes the UTC
date). No wall-clock reads affect the output. Tender pages do not print a
relative "closes in N days" in static text (that would rewrite every page every
day); a tiny inline script computes it from the closing date in the browser.
"""
from __future__ import annotations

import argparse
import html
import json
import os
import re
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

# --------------------------------------------------------------------------
# configuration

SITE = "https://deadlinebiddesk.com"
HOST = "deadlinebiddesk.com"
EMAIL = "ruben@deadlinebiddesk.com"
API = "https://ocds-api.etenders.gov.za/api/OCDSReleases"
USER_AGENT = ("DeadlineBidDesk-TenderSite/1.0 (+https://deadlinebiddesk.com; "
              "daily public listing refresh; ruben@deadlinebiddesk.com)")
INDEXNOW_ENDPOINT = "https://api.indexnow.org/indexnow"
ETENDERS_SEARCH = "https://www.etenders.gov.za/Home/opportunities?id=1"

ROOT = Path(__file__).resolve().parent
TENDERS_DIR = "tenders"

PAGE_SIZE = 100
MAX_PAGES_PER_DAY = 40            # 4,000 releases advertised on one day: never seen
MIN_INTERVAL = 0.2                # seconds between request starts, global (politeness)
WORKERS = 4                       # one-day windows fetched in parallel
HTTP_TIMEOUT = 60
HUB_ROWS = 200                    # rows per hub page before paginating
RELATED_MAX = 8
CATEGORY_HUB_MIN = 3              # free-text procurement categories need >= 3 tenders
MAX_TENDER_PAGES = 8000           # hard cap on per-tender pages per run
MIN_OPEN_TENDERS = 150            # fewer than this = API failure, do not publish
MIN_OPEN_RATIO = 0.5              # open count below 50% of last run = API failure
MAX_LOST_RATIO = 0.6              # more than 60% of records unreadable = API failure
INDEXNOW_MAX = 10000

PROVINCES = [
    ("Eastern Cape", "eastern-cape"),
    ("Free State", "free-state"),
    ("Gauteng", "gauteng"),
    ("KwaZulu-Natal", "kwazulu-natal"),
    ("Limpopo", "limpopo"),
    ("Mpumalanga", "mpumalanga"),
    ("North West", "north-west"),
    ("Northern Cape", "northern-cape"),
    ("Western Cape", "western-cape"),
    ("National", "national"),
]
PROVINCE_SLUG = dict(PROVINCES)

# Province stated in the buyer's own name. Only explicit names and the metros
# whose names unambiguously belong to one province. Order matters: longer
# names first so "Northern Cape" is not read as anything shorter.
BUYER_PROVINCE_PATTERNS = [
    (r"\bkwa-?zulu[\s-]*natal\b|\bKZN\b", "KwaZulu-Natal"),
    (r"\beastern\s+cape\b", "Eastern Cape"),
    (r"\bwestern\s+cape\b", "Western Cape"),
    (r"\bnorthern\s+cape\b", "Northern Cape"),
    (r"\bnorth[\s-]+west\b", "North West"),
    (r"\bfree\s+state\b", "Free State"),
    (r"\bgauteng\b", "Gauteng"),
    (r"\blimpopo\b", "Limpopo"),
    (r"\bmpumalanga\b", "Mpumalanga"),
    (r"\bcity\s+of\s+cape\s+town\b", "Western Cape"),
    (r"\bcity\s+of\s+johannesburg\b|\bcity\s+of\s+tshwane\b|\bekurhuleni\b",
     "Gauteng"),
    (r"\bethekwini\b", "KwaZulu-Natal"),
    (r"\bnelson\s+mandela\s+bay\b|\bbuffalo\s+city\b", "Eastern Cape"),
    (r"\bmangaung\b", "Free State"),
]

MAIN_CATEGORIES = {
    "services": ("Services", "a service provider"),
    "goods": ("Goods", "a supplier"),
    "works": ("Works", "a contractor"),
}

CLOSED_STATUSES = {"cancelled", "canceled", "complete", "completed",
                   "unsuccessful", "withdrawn", "awarded"}

MONTHS = ["January", "February", "March", "April", "May", "June", "July",
          "August", "September", "October", "November", "December"]


class FetchAbort(Exception):
    """The API failed badly enough that publishing would damage the site."""


# --------------------------------------------------------------------------
# small helpers

e = html.escape


def long_date(d: date) -> str:
    return f"{d.day} {MONTHS[d.month - 1]} {d.year}"


def short_date(d: date) -> str:
    return f"{d.day} {MONTHS[d.month - 1][:3]} {d.year}"


def parse_dt(raw) -> tuple[date | None, str]:
    """Return (date, 'HH:MM' or '') from an OCDS timestamp string."""
    if not raw or not isinstance(raw, str):
        return None, ""
    try:
        d = date.fromisoformat(raw[:10])
    except ValueError:
        return None, ""
    hhmm = raw[11:16] if len(raw) >= 16 and raw[10] == "T" else ""
    if hhmm == "00:00":
        hhmm = ""
    return d, hhmm


def clean(text, limit: int | None = None) -> str:
    text = re.sub(r"\s+", " ", str(text or "")).strip()
    if limit and len(text) > limit:
        cut = text[:limit].rsplit(" ", 1)[0]
        text = cut.rstrip(" ,;:-.") + "…"
    return text


def slugify(text: str, limit: int = 60) -> str:
    s = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return (s[:limit].rstrip("-")) or "x"


def ocid_slug(ocid: str) -> str:
    return slugify(ocid, 80)


def days_label(n: int) -> str:
    if n <= 0:
        return "closes today"
    if n == 1:
        return "closes tomorrow"
    return f"closes in {n} days"


def mailto(subject: str) -> str:
    return f"mailto:{EMAIL}?subject=" + urllib.parse.quote(subject, safe="")


# --------------------------------------------------------------------------
# fetching

class Client:
    """Thread-safe, globally rate-limited API client with budgets."""

    def __init__(self, max_requests: int, max_seconds: int):
        self.max_requests = max_requests
        self.deadline = time.monotonic() + max_seconds
        self.requests = 0
        self.failures = 0
        self.consecutive_net_failures = 0
        self.http_codes: Counter = Counter()
        self._last = 0.0
        self._lock = threading.Lock()
        self.aborted: str | None = None

    def _reserve_slot(self):
        with self._lock:
            if self.aborted:
                raise FetchAbort(self.aborted)
            if self.requests >= self.max_requests:
                self.aborted = f"request budget of {self.max_requests} exhausted"
            elif time.monotonic() > self.deadline:
                self.aborted = "time budget exhausted"
            elif self.consecutive_net_failures >= 15:
                self.aborted = "15 consecutive network failures: API looks down"
            if self.aborted:
                raise FetchAbort(self.aborted)
            self.requests += 1
            now = time.monotonic()
            slot = max(now, self._last + MIN_INTERVAL)
            self._last = slot
        if slot > now:
            time.sleep(slot - now)

    def _count(self, code, net_fail: bool | None):
        with self._lock:
            self.http_codes[code] += 1
            if self.requests % 250 == 0:
                print(f"    .. {self.requests} requests, codes {dict(self.http_codes)}",
                      flush=True)
            if net_fail is True:
                self.consecutive_net_failures += 1
            elif net_fail is False:
                self.consecutive_net_failures = 0

    def get(self, params: dict) -> list | None:
        """One API page. Returns the releases list, or None if it failed.

        HTTP 500 is NOT retried here: it is almost always a poison record,
        and fetch_block() re-requests the same offsets in smaller pages,
        which doubles as the retry for a transient 500.
        """
        url = API + "?" + urllib.parse.urlencode(params)
        net_tries = 0
        while True:
            self._reserve_slot()
            req = urllib.request.Request(url, headers={
                "User-Agent": USER_AGENT, "Accept": "application/json"})
            try:
                with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
                    raw = resp.read()
                payload = json.loads(raw.decode("utf-8"))
                rels = payload.get("releases")
                if not isinstance(rels, list):
                    raise ValueError("no releases list")
                self._count(200, False)
                return rels
            except urllib.error.HTTPError as exc:
                if exc.code in (429, 502, 503, 504):
                    self._count(exc.code, None)
                    net_tries += 1
                    if net_tries > 3:
                        break
                    time.sleep((5, 20, 60)[net_tries - 1])
                    continue
                self._count(exc.code, False)
                break                              # 500 / other 4xx: give up
            except (ValueError, UnicodeDecodeError):
                self._count("bad-json", False)
                break
            except (urllib.error.URLError, TimeoutError, OSError):
                self._count("net", True)
                net_tries += 1
                if net_tries > 3:
                    break
                time.sleep((2, 5, 15)[net_tries - 1])
        with self._lock:
            self.failures += 1
        return None


def fetch_block(client: Client, day: str, size: int, page: int):
    """Fetch the records at offsets of page `page` of size `size`.

    Returns (releases, ended, lost) where ended means the API reported no rows
    at all for this block and lost counts unrecoverable size-1 pages.
    """
    params = {"PageNumber": page, "PageSize": size, "dateFrom": day, "dateTo": day}
    rels = client.get(params)
    if rels is not None:
        return rels, len(rels) == 0, 0
    if size == 1:
        return [], False, 1
    sub = max(1, size // 10)
    out: list = []
    lost = 0
    first = (page - 1) * (size // sub) + 1
    for sp in range(first, first + size // sub):
        r, ended, l = fetch_block(client, day, sub, sp)
        lost += l
        out.extend(r)
        if ended:
            # A successful empty page means we are past the last record of
            # the day: stop here and tell the caller the day is finished.
            return out, True, lost
    return out, False, lost


def fetch_all(client: Client, today: date, back_days: int, forward_days: int,
              log=print):
    """Walk one-day windows. Returns (releases, per-day stats)."""
    start = today - timedelta(days=back_days)
    days = [(start + timedelta(days=i)).isoformat()
            for i in range(back_days + forward_days + 1)]

    def one_day(ds: str):
        got: list = []
        lost, pages = 0, 0
        for page in range(1, MAX_PAGES_PER_DAY + 1):
            rels, ended, l = fetch_block(client, ds, PAGE_SIZE, page)
            pages += 1
            lost += l
            got.extend(rels)
            if ended:
                break
        log(f"  {ds}: {len(got):4d} releases, {lost:3d} lost "
            f"({client.requests} requests so far)")
        return ds, got, {"releases": len(got), "lost": lost, "pages": pages}

    results: dict[str, tuple] = {}
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        futures = [pool.submit(one_day, ds) for ds in days]
        for fut in futures:
            ds, got, st = fut.result()          # re-raises FetchAbort
            results[ds] = (got, st)
    releases: list = []
    day_stats: dict[str, dict] = {}
    for ds in days:                             # fixed order => deterministic
        got, st = results[ds]
        releases.extend(got)
        day_stats[ds] = st
    return releases, day_stats


# --------------------------------------------------------------------------
# normalising

def province_for(tender: dict, buyer: str) -> tuple[str, str]:
    raw = clean(tender.get("province"))
    if raw:
        for name, _slug in PROVINCES:
            if raw.lower().replace(" ", "") == name.lower().replace(" ", ""):
                return name, "listed"
        if raw.lower() in ("kzn", "kwazulu natal"):
            return "KwaZulu-Natal", "listed"
        return raw, "listed"
    for pat, name in BUYER_PROVINCE_PATTERNS:
        if re.search(pat, buyer, re.I):
            return name, "buyer"
    return "", ""


def normalise(rel: dict) -> dict | None:
    tender = rel.get("tender") or {}
    ocid = clean(rel.get("ocid"))
    if not ocid or not re.fullmatch(r"[A-Za-z0-9._-]+", ocid):
        return None
    period = tender.get("tenderPeriod") or {}
    close_d, close_t = parse_dt(period.get("endDate"))
    if close_d is None:
        return None
    open_d, _ = parse_dt(period.get("startDate"))
    rel_d, _ = parse_dt(rel.get("date"))
    entity = tender.get("procuringEntity") or {}
    buyer = clean(entity.get("name") or (rel.get("buyer") or {}).get("name"))
    province, prov_src = province_for(tender, buyer)
    briefing = tender.get("briefingSession")
    brief = None
    if isinstance(briefing, dict) and (briefing.get("isSession") or briefing.get("date")):
        bd, bt = parse_dt(briefing.get("date"))
        brief = {
            "compulsory": bool(briefing.get("compulsory")),
            "date": bd.isoformat() if bd else "",
            "time": bt,
            "venue": clean(briefing.get("venue"), 300),
        }
    docs = []
    for doc in tender.get("documents") or []:
        url = (doc or {}).get("url") or ""
        if not url.startswith("https://"):
            continue
        docs.append({
            "title": clean(doc.get("title") or doc.get("description") or "Tender document", 160),
            "url": url,
            "format": clean(doc.get("format"), 10).lower(),
            "published": (parse_dt(doc.get("datePublished"))[0] or "") and
                         parse_dt(doc.get("datePublished"))[0].isoformat(),
        })
    docs.sort(key=lambda x: (x["published"], x["title"], x["url"]))
    main_cat = clean(tender.get("mainProcurementCategory")).lower()
    return {
        "ocid": ocid,
        "tender_id": clean(tender.get("id"), 40),
        "ref": clean(tender.get("title"), 120),
        "description": clean(tender.get("description"), 1500),
        "buyer": buyer,
        "province": province,
        "province_source": prov_src,
        "delivery_location": clean(tender.get("deliveryLocation"), 200),
        "main_category": main_cat if main_cat in MAIN_CATEGORIES else "",
        "category": clean(tender.get("category"), 120),
        "status": clean(tender.get("status")).lower(),
        "method": clean(tender.get("procurementMethodDetails"), 120),
        "special_conditions": clean(tender.get("specialConditions"), 600),
        "release_date": rel_d.isoformat() if rel_d else "",
        "open_date": open_d.isoformat() if open_d else "",
        "close_date": close_d.isoformat(),
        "close_time": close_t,
        "briefing": brief,
        "documents": docs[:20],
    }


def dedupe(records: list[dict]) -> list[dict]:
    """Keep the latest release per ocid (amendments re-issue the same ocid)."""
    best: dict[str, dict] = {}
    for r in records:
        cur = best.get(r["ocid"])
        key = (r["release_date"], r["close_date"], json.dumps(r, sort_keys=True))
        if cur is None or key > (cur["release_date"], cur["close_date"],
                                 json.dumps(cur, sort_keys=True)):
            best[r["ocid"]] = r
    return list(best.values())


def is_open(r: dict, today: date) -> bool:
    if r["status"] in CLOSED_STATUSES:
        return False
    return date.fromisoformat(r["close_date"]) >= today


# --------------------------------------------------------------------------
# carry-over of previously published tenders (for days with lost records)

DATA_RE = re.compile(
    r'<script type="application/json" id="tender-data">(.*?)</script>', re.S)


def load_previous(root: Path) -> tuple[dict[str, dict], dict]:
    prev: dict[str, dict] = {}
    tdir = root / TENDERS_DIR / "t"
    if tdir.is_dir():
        for f in sorted(tdir.glob("*.html")):
            m = DATA_RE.search(f.read_text(encoding="utf-8"))
            if not m:
                continue
            try:
                rec = json.loads(m.group(1).replace("<\\/", "</"))
                prev[rec["ocid"]] = rec
            except (ValueError, KeyError):
                continue
    manifest = {}
    mf = root / TENDERS_DIR / "manifest.json"
    if mf.exists():
        try:
            manifest = json.loads(mf.read_text(encoding="utf-8"))
        except ValueError:
            manifest = {}
    return prev, manifest


# --------------------------------------------------------------------------
# rendering

NAV = [
    ("/index.html", "Home"),
    ("/south-africa.html", "South Africa"),
    ("/tenders/index.html", "SA tenders"),
    ("/business-plans.html", "Business plans"),
    ("/terms.html", "Terms"),
    ("/privacy.html", "Privacy"),
]

CLOSES_JS = """<script>
(function () {
  var t = new Date(), today = Date.UTC(t.getFullYear(), t.getMonth(), t.getDate());
  document.querySelectorAll("[data-closes]").forEach(function (el) {
    var p = el.getAttribute("data-closes").split("-");
    var n = Math.round((Date.UTC(+p[0], +p[1] - 1, +p[2]) - today) / 864e5);
    el.textContent = n < 0 ? "this tender has closed" : n === 0 ? "closes today" :
      n === 1 ? "closes tomorrow" : "closes in " + n + " days";
  });
})();
</script>
"""


def page(path: str, title: str, description: str, body: str, *,
         robots: str = "index,follow", canonical: bool = True,
         extra_head: str = "", tail: str = "") -> str:
    nav = "\n".join(
        f'        <li><a href="{href}"'
        + (' aria-current="page"' if href == "/tenders/index.html" and path.startswith("/tenders/") else "")
        + f">{label}</a></li>"
        for href, label in NAV)
    canon = f'<link rel="canonical" href="{e(SITE + path)}">\n' if canonical else ""
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="{robots}">
<meta name="description" content="{e(description)}">
<title>{e(title)}</title>
{canon}{extra_head}<link rel="stylesheet" href="/style.css">
</head>
<body>
<a class="skip-link" href="#main">Skip to content</a>

<header class="site-header">
  <div class="wrap">
    <p class="site-title"><a href="/index.html">Deadline Bid Desk</a></p>
    <p class="site-strap">Bid writing for live public tenders. UK, US and South Africa.</p>
    <nav aria-label="Main">
      <ul>
{nav}
      </ul>
    </nav>
  </div>
</header>

<main id="main">
  <div class="wrap">
{body}
  </div>
</main>

<footer class="site-footer">
  <div class="wrap">
    <p>Deadline Bid Desk &mdash; Ruben Mocke, sole proprietor, Mossel Bay,
    South Africa. All work is delivered in writing. Tender listings are
    republished from the National Treasury eTenders portal as public
    procurement information; always confirm details in the official tender
    documents.</p>
    <ul>
      <li><a href="/index.html">Home</a></li>
      <li><a href="/south-africa.html">South Africa</a></li>
      <li><a href="/tenders/index.html">SA tenders</a></li>
      <li><a href="/business-plans.html">Business plans</a></li>
      <li><a href="/terms.html">Terms</a></li>
      <li><a href="/privacy.html">Privacy</a></li>
      <li><a href="mailto:{EMAIL}">{EMAIL}</a></li>
    </ul>
  </div>
</footer>
{tail}
</body>
</html>
"""


def cta(subject: str, lead: str = "Bidding on this?") -> str:
    return f"""
    <div class="note">
      <p><strong>{e(lead)}</strong> Send the tender number for a free one-page
      scoring map: <a href="{e(mailto(subject))}">{EMAIL}</a></p>
      <p><a href="/south-africa.html">How the South African tender-response
      service works</a> &middot; <a href="/business-plans.html">Funding business
      plans</a></p>
    </div>
"""


def tender_url(r: dict) -> str:
    return f"/{TENDERS_DIR}/t/{ocid_slug(r['ocid'])}.html"


def province_url(name: str, n: int = 1) -> str:
    slug = PROVINCE_SLUG.get(name) or slugify(name)
    return f"/{TENDERS_DIR}/province/{slug}{'' if n == 1 else f'-{n}'}.html"


def category_key_url(key: str, n: int = 1) -> str:
    return f"/{TENDERS_DIR}/category/{key}{'' if n == 1 else f'-{n}'}.html"


def display_title(r: dict) -> str:
    return r["description"] or (f"Tender {r['ref']}" if r["ref"] else r["ocid"])


def category_label(r: dict) -> str:
    return MAIN_CATEGORIES[r["main_category"]][0] if r["main_category"] else ""


def tender_rows(rows: list[dict], today: date, show_province: bool = True) -> str:
    out = ["""    <div class="table-scroll">
      <table>
        <thead>
          <tr>
            <th scope="col">Tender</th>
            <th scope="col">Buyer</th>""" + ("""
            <th scope="col">Province</th>""" if show_province else "") + """
            <th scope="col">Closes</th>
          </tr>
        </thead>
        <tbody>"""]
    for r in rows:
        cd = date.fromisoformat(r["close_date"])
        n = (cd - today).days
        ref = f'<br><span class="sub">Ref {e(r["ref"])}</span>' if r["ref"] else ""
        prov = e(r["province"]) if r["province"] else "&mdash;"
        out.append(f"""          <tr>
            <td><a href="{tender_url(r)}">{e(clean(display_title(r), 160))}</a>{ref}</td>
            <td>{e(r["buyer"]) or "&mdash;"}</td>""" + (f"""
            <td>{prov}</td>""" if show_province else "") + f"""
            <td class="num">{e(short_date(cd))}<br><span class="sub">{e(days_label(n))}</span></td>
          </tr>""")
    out.append("""        </tbody>
      </table>
    </div>""")
    return "\n".join(out)


def sort_key(r: dict):
    return (r["close_date"], r["close_time"] or "99:99", r["buyer"].lower(), r["ocid"])


def summary_line(r: dict) -> str:
    """Plain-English one-liner built only from fields present."""
    who = r["buyer"] or "The buyer"
    want = MAIN_CATEGORIES[r["main_category"]][1] if r["main_category"] else "bids"
    desc = clean(r["description"], 220).rstrip(" .;,:")
    cd = date.fromisoformat(r["close_date"])
    when = long_date(cd) + (f" at {r['close_time']}" if r["close_time"] else "")
    if desc:
        s = f"{who} is inviting {'bids from ' + want if r['main_category'] else 'bids'} for: “{desc}”."
    else:
        s = f"{who} is inviting {'bids from ' + want if r['main_category'] else 'bids'}."
    s += f" Submissions close on {when}."
    if r["briefing"] and r["briefing"].get("compulsory"):
        s += " A compulsory briefing session is listed."
    return s


def related_for(r: dict, by_buyer: dict, by_cat: dict) -> tuple[list[dict], list[dict]]:
    """Related tenders that close on or after this one (so the list stays put
    while this page exists): same buyer first, then same category."""
    def pick(pool, exclude, limit):
        out = []
        for x in pool:
            if x["ocid"] in exclude or x["close_date"] < r["close_date"]:
                continue
            out.append(x)
            if len(out) >= limit:
                break
        return out
    seen = {r["ocid"]}
    same_buyer = pick(by_buyer.get(r["buyer"], []), seen, 5) if r["buyer"] else []
    seen |= {x["ocid"] for x in same_buyer}
    cat_key = cat_keys(r)[-1] if cat_keys(r) else None
    same_cat = pick(by_cat.get(cat_key, []), seen, RELATED_MAX - len(same_buyer)) if cat_key else []
    return same_buyer, same_cat


def cat_keys(r: dict) -> list[str]:
    keys = []
    if r["main_category"]:
        keys.append(r["main_category"])
    if r["category"]:
        keys.append("c-" + slugify(r["category"]))
    return keys


def render_tender(r: dict, today: date, related: tuple[list, list],
                  cat_names: dict[str, str], hub_cats: set[str]) -> str:
    title = display_title(r)
    cd = date.fromisoformat(r["close_date"])
    close_txt = long_date(cd) + (f", {r['close_time']}" if r["close_time"] else "")
    adv = date.fromisoformat(r["open_date"]) if r["open_date"] else None
    buyer = r["buyer"] or "Not stated"
    head_title = f"{clean(title, 70)} - {clean(buyer, 40)} | closes {short_date(cd)}"
    meta = clean(
        f"Tender {r['ref'] or r['tender_id']} from {buyer}: {clean(title, 150).rstrip(' .;,:')}. "
        + (f"Advertised {short_date(adv)}, " if adv else "")
        + f"closes {short_date(cd)}"
        + (f" {r['close_time']}" if r["close_time"] else "")
        + ". Official eTenders documents, briefing details and related tenders.", 300)

    facts = []
    def fact(label, value_html):
        facts.append(f'          <tr><th scope="row">{label}</th><td>{value_html}</td></tr>')
    if r["ref"]:
        fact("Tender number", e(r["ref"]))
    if r["tender_id"]:
        fact("eTenders ID", e(r["tender_id"]))
    fact("Buyer", e(buyer))
    if r["province"]:
        purl = province_url(r["province"])
        note = ' <span class="sub">(from the buyer&#39;s name)</span>' if r["province_source"] == "buyer" else ""
        fact("Province", f'<a href="{purl}">{e(r["province"])}</a>{note}')
    if r["delivery_location"]:
        fact("Delivery location", e(r["delivery_location"]))
    cats = []
    for k in cat_keys(r):
        label = cat_names[k]
        cats.append(f'<a href="{category_key_url(k)}">{e(label)}</a>' if k in hub_cats else e(label))
    if cats:
        fact("Category", " &middot; ".join(cats))
    if r["method"]:
        fact("Procurement method", e(r["method"]))
    if adv:
        fact("Advertised", e(long_date(adv)))
    fact("Closing date",
         f'<strong>{e(close_txt)}</strong><br><span class="sub" data-closes="{cd.isoformat()}"></span>')

    b = r["briefing"]
    if b:
        txt = ("Compulsory" if b["compulsory"] else "Non-compulsory") + " briefing session"
        if b["date"]:
            bd = date.fromisoformat(b["date"])
            txt += " on " + long_date(bd) + (f" at {b['time']}" if b["time"] else "")
        if b["venue"]:
            txt += f". Venue: {b['venue']}"
        briefing_html = f"<p><strong>Briefing:</strong> {e(txt)}.</p>"
    else:
        briefing_html = ("<p><strong>Briefing session:</strong> the eTenders listing "
                         "does not include briefing or site-meeting details for this "
                         "tender. Check the tender documents below for any compulsory "
                         "briefing before you plan your bid.</p>")
    special = (f"<p><strong>Special conditions (as listed):</strong> {e(r['special_conditions'])}</p>"
               if r["special_conditions"] and r["special_conditions"].lower() not in ("n/a", "na", "none", "-") else "")

    if r["documents"]:
        docs = "\n".join(
            f'      <li><a href="{e(d["url"])}" rel="nofollow">{e(d["title"])}</a>'
            + (f' <span class="sub">({e(d["format"].upper())})</span>' if d["format"] else "")
            + "</li>" for d in r["documents"])
        docs_html = f"""    <h2>Official tender documents</h2>
    <p>Downloaded directly from the National Treasury eTenders portal:</p>
    <ul>
{docs}
    </ul>
    <p>Not working? Search for tender number <strong>{e(r['ref'] or r['tender_id'])}</strong>
    on the <a href="{ETENDERS_SEARCH}" rel="nofollow">eTenders opportunities page</a>.</p>"""
    else:
        docs_html = f"""    <h2>Official tender documents</h2>
    <p>Search for tender number <strong>{e(r['ref'] or r['tender_id'])}</strong> on the
    <a href="{ETENDERS_SEARCH}" rel="nofollow">eTenders opportunities page</a>.</p>"""

    same_buyer, same_cat = related
    rel_html = ""
    if same_buyer:
        rel_html += f"\n    <h2>More open tenders from {e(buyer)}</h2>\n    <ul>\n" + "\n".join(
            f'      <li><a href="{tender_url(x)}">{e(clean(display_title(x), 140))}</a>'
            f' <span class="sub">&mdash; closes {e(short_date(date.fromisoformat(x["close_date"])))}</span></li>'
            for x in same_buyer) + "\n    </ul>"
    if same_cat:
        k = cat_keys(r)[-1]
        rel_html += f"\n    <h2>Other open {e(cat_names[k].lower())} tenders closing around the same time</h2>\n    <ul>\n" + "\n".join(
            f'      <li><a href="{tender_url(x)}">{e(clean(display_title(x), 140))}</a>'
            f' <span class="sub">&mdash; {e(x["buyer"])}, closes {e(short_date(date.fromisoformat(x["close_date"])))}</span></li>'
            for x in same_cat) + "\n    </ul>"

    hub_links = ['<a href="/tenders/index.html">All open SA tenders</a>',
                 '<a href="/tenders/closing-this-week.html">Closing this week</a>']
    if r["province"]:
        hub_links.append(f'<a href="{province_url(r["province"])}">{e(r["province"])} tenders</a>')
    for k in cat_keys(r):
        if k in hub_cats:
            hub_links.append(f'<a href="{category_key_url(k)}">{e(cat_names[k])} tenders</a>')

    data = json.dumps(r, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    data = data.replace("</", "<\\/").replace("<!--", "<\\!--")

    body = f"""
    <p class="sub"><a href="/tenders/index.html">SA tenders</a>{' &rsaquo; <a href="' + province_url(r["province"]) + '">' + e(r["province"]) + '</a>' if r["province"] else ''}</p>

    <h1>{e(clean(title, 300))}</h1>

    <p class="lede">{e(summary_line(r))}</p>

    <div class="table-scroll">
      <table>
        <caption>Tender details</caption>
        <tbody>
{chr(10).join(facts)}
        </tbody>
      </table>
    </div>

    {briefing_html}
    {special}
{cta(f"Scoring map request: tender {r['ref'] or r['tender_id']}")}
{docs_html}
{rel_html}

    <p>{' &middot; '.join(hub_links)}</p>

    <p class="sub">Source: National Treasury eTenders OCDS release {e(r['ocid'])}.
    This page is removed automatically after the closing date. Always confirm
    the closing date, briefing and returnable documents in the official tender
    documents.</p>
<script type="application/json" id="tender-data">{data}</script>"""
    return page(tender_url(r), head_title, meta, body, tail=CLOSES_JS)


def render_hub(path: str, h1: str, title: str, description: str, intro: str,
               rows: list[dict], today: date, page_no: int, page_count: int,
               url_for, subject: str, show_province: bool = True,
               extra: str = "") -> str:
    pager = ""
    if page_count > 1:
        links = []
        for n in range(1, page_count + 1):
            if n == page_no:
                links.append(f"<strong>{n}</strong>")
            else:
                links.append(f'<a href="{url_for(n)}">{n}</a>')
        pager = f'\n    <p>Page {page_no} of {page_count}: {" ".join(links)}</p>'
    head = ""
    if page_no > 1:
        head += f'<link rel="prev" href="{e(SITE + url_for(page_no - 1))}">\n'
    if page_no < page_count:
        head += f'<link rel="next" href="{e(SITE + url_for(page_no + 1))}">\n'
    body = f"""
    <p class="sub"><a href="/tenders/index.html">SA tenders</a></p>

    <h1>{e(h1)}{f" (page {page_no})" if page_no > 1 else ""}</h1>

    {intro}
{extra}{cta(subject)}
{pager}
{tender_rows(rows, today, show_province) if rows else "    <p>No open tenders in this group today.</p>"}
{pager}

    <p><a href="/tenders/index.html">All open SA tenders</a> &middot;
    <a href="/tenders/closing-this-week.html">Closing this week</a> &middot;
    <a href="/za-closing-soon.html">Closing in the next 21 days</a></p>
"""
    t = title if page_no == 1 else f"{title} (page {page_no})"
    return page(path, t, description, body, extra_head=head)


def paginate(rows: list, size: int = HUB_ROWS) -> list[list]:
    if not rows:
        return [[]]
    return [rows[i:i + size] for i in range(0, len(rows), size)]


# --------------------------------------------------------------------------
# build

def build(records: list[dict], today: date, stats: dict) -> dict[str, str]:
    """Return {relative file path: content} for everything under tenders/."""
    files: dict[str, str] = {}
    upd = long_date(today)
    open_t = sorted(records, key=sort_key)

    by_buyer: dict[str, list] = defaultdict(list)
    by_cat: dict[str, list] = defaultdict(list)
    by_prov: dict[str, list] = defaultdict(list)
    cat_names: dict[str, str] = {}
    for r in open_t:
        by_buyer[r["buyer"]].append(r)
        if r["province"]:
            by_prov[r["province"]].append(r)
        for k in cat_keys(r):
            by_cat[k].append(r)
            cat_names[k] = MAIN_CATEGORIES[k][0] if k in MAIN_CATEGORIES else r["category"]
    hub_cats = {k for k, v in by_cat.items()
                if k in MAIN_CATEGORIES or len(v) >= CATEGORY_HUB_MIN}
    known_prov = [p for p, _ in PROVINCES if p in by_prov]
    other_prov = sorted(p for p in by_prov if p not in PROVINCE_SLUG)
    prov_order = known_prov + other_prov

    week_end = today + timedelta(days=6)
    this_week = [r for r in open_t if r["close_date"] <= week_end.isoformat()]
    new_7 = [r for r in open_t if r["open_date"] and r["open_date"] >= (today - timedelta(days=6)).isoformat()]

    # --- tender pages
    for r in open_t[:MAX_TENDER_PAGES]:
        rel = related_for(r, by_buyer, by_cat)
        files[tender_url(r).lstrip("/")] = render_tender(r, today, rel, cat_names, hub_cats)

    # --- province hubs
    for p in prov_order:
        rows = by_prov[p]
        chunks = paginate(rows)
        derived = sum(1 for r in rows if r["province_source"] == "buyer")
        note = ""
        if derived:
            note = (f"\n    <p class=\"sub\">The eTenders data feed currently does not carry a province "
                    f"field, so this list holds tenders whose buyer name places them in "
                    f"{e(p)} (for example a provincial department or a metro). Tenders from "
                    f"national departments, SOEs and municipalities whose names do not state a "
                    f"province are listed on the <a href=\"/tenders/index.html\">main tenders page</a> "
                    f"and in the category lists.</p>\n")
        for i, chunk in enumerate(chunks, 1):
            path = province_url(p, i)
            files[path.lstrip("/")] = render_hub(
                path, f"Open government tenders in {p}",
                f"{p} government tenders open now ({len(rows)}) - closing dates | Deadline Bid Desk",
                clean(f"{len(rows)} open {p} public-sector tenders from eTenders, soonest closing first: "
                      f"tender number, buyer and closing date. Updated {upd}.", 300),
                f"""<p class="lede"><strong>Updated {e(upd)}.</strong> {len(rows)} open tenders
    for buyers in {e(p)}, from the National Treasury eTenders portal, soonest
    closing first. Each links to a page with the official tender documents.</p>""",
                chunk, today, i, len(chunks), lambda n, p=p: province_url(p, n),
                f"Scoring map request: {p} tender", show_province=False, extra=note)

    # --- category hubs
    cat_order = [k for k in ("services", "goods", "works") if k in by_cat] + sorted(
        (k for k in hub_cats if k not in MAIN_CATEGORIES), key=lambda k: cat_names[k].lower())
    for k in cat_order:
        rows = by_cat[k]
        name = cat_names[k]
        chunks = paginate(rows)
        for i, chunk in enumerate(chunks, 1):
            path = category_key_url(k, i)
            files[path.lstrip("/")] = render_hub(
                path, f"Open SA tenders: {name}",
                f"{name} tenders in South Africa open now ({len(rows)}) | Deadline Bid Desk",
                clean(f"{len(rows)} open South African government {name.lower()} tenders from eTenders, "
                      f"soonest closing first, with buyer and closing date. Updated {upd}.", 300),
                f"""<p class="lede"><strong>Updated {e(upd)}.</strong> {len(rows)} open
    South African public-sector tenders in the <strong>{e(name.lower())}</strong>
    procurement category, from the National Treasury eTenders portal, soonest
    closing first.</p>""",
                chunk, today, i, len(chunks), lambda n, k=k: category_key_url(k, n),
                f"Scoring map request: {name} tender")

    # --- closing this week
    path = f"/{TENDERS_DIR}/closing-this-week.html"
    files[path.lstrip("/")] = render_hub(
        path, "SA tenders closing this week",
        f"SA government tenders closing this week ({len(this_week)}) | Deadline Bid Desk",
        clean(f"{len(this_week)} South African government tenders closing between {short_date(today)} "
              f"and {short_date(week_end)}, from eTenders: tender number, buyer, province and closing date.", 300),
        f"""<p class="lede"><strong>Updated {e(upd)}.</strong> {len(this_week)} open
    tenders on the eTenders portal close between {e(short_date(today))} and
    {e(short_date(week_end))}, soonest first. If you are bidding on one of
    these, time is short &mdash; send the tender number today.</p>""",
        this_week, today, 1, 1, lambda n: path, "Scoring map request: tender closing this week")

    # --- index
    prov_rows = "\n".join(
        f'          <tr><td><a href="{province_url(p)}">{e(p)}</a></td><td class="num">{len(by_prov[p])}</td></tr>'
        for p in prov_order)
    cat_rows = "\n".join(
        f'          <tr><td><a href="{category_key_url(k)}">{e(cat_names[k])}</a></td><td class="num">{len(by_cat[k])}</td></tr>'
        for k in cat_order)
    no_prov = sum(1 for r in open_t if not r["province"])
    no_cat = sum(1 for r in open_t if not cat_keys(r))
    soon = this_week[:25]
    recent = sorted(new_7, key=lambda r: (r["open_date"], r["ocid"]), reverse=True)[:25]
    recent = sorted(recent, key=sort_key)
    body = f"""
    <h1>Open South African government tenders</h1>

    <p class="lede"><strong>Updated {e(upd)}.</strong> Every open tender
    advertised on the National Treasury eTenders portal in the last 60 days,
    refreshed daily: <strong>{len(open_t):,} open tenders</strong>,
    <strong>{len(this_week):,}</strong> closing in the next seven days and
    <strong>{len(new_7):,}</strong> advertised in the past week.</p>

    <p>Each tender has its own page with the tender number, buyer, closing
    date, briefing details where the portal lists them, and direct links to
    the official tender documents. Pages are removed once a tender closes.</p>
{cta("Scoring map request: SA tender", "Bidding on a tender?")}
    <h2>Closing this week</h2>
{tender_rows(soon, today) if soon else "    <p>No tenders close in the next seven days.</p>"}
    <p><a href="/tenders/closing-this-week.html">All {len(this_week):,} tenders closing this week</a></p>

    <h2>By province</h2>
    <div class="table-scroll">
      <table>
        <thead><tr><th scope="col">Province</th><th scope="col" class="num">Open tenders</th></tr></thead>
        <tbody>
{prov_rows}
        </tbody>
      </table>
    </div>
    <p class="sub">{no_prov:,} open tenders do not state a province: the eTenders
    data feed currently has no province field, so a province is shown only when
    the buyer&#39;s own name gives it (provincial departments and metros).
    National departments and state-owned companies are listed by category.</p>

    <h2>By procurement category</h2>
    <div class="table-scroll">
      <table>
        <thead><tr><th scope="col">Category</th><th scope="col" class="num">Open tenders</th></tr></thead>
        <tbody>
{cat_rows}
        </tbody>
      </table>
    </div>
    {f'<p class="sub">{no_cat:,} open tenders have no procurement category on eTenders.</p>' if no_cat else ''}

    <h2>Recently advertised</h2>
{tender_rows(recent, today) if recent else "    <p>Nothing advertised in the past seven days.</p>"}

    <p>Source: the National Treasury eTenders OCDS public API
    (ocds-api.etenders.gov.za), refreshed automatically every day. Listing data
    is republished as public procurement information; always verify closing
    dates and requirements in the official tender documents.</p>

    <p><a href="/za-closing-soon.html">Tenders closing in the next 21 days</a> &middot;
    <a href="/south-africa.html">South Africa services</a> &middot;
    <a href="/business-plans.html">Funding business plans</a></p>
"""
    path = f"/{TENDERS_DIR}/index.html"
    files[path.lstrip("/")] = page(
        path, f"Open SA government tenders ({len(open_t):,}) - eTenders, updated daily | Deadline Bid Desk",
        clean(f"{len(open_t):,} open South African government tenders from eTenders, updated {upd}: "
              f"{len(this_week):,} closing this week. Browse by province and category, with official "
              f"tender documents.", 300), body)

    # --- closed note
    path = f"/{TENDERS_DIR}/closed.html"
    files[path.lstrip("/")] = page(
        path, "Tender closed - Deadline Bid Desk",
        "Tender pages on this site are removed automatically after the tender's closing date.",
        """
    <h1>This tender has closed</h1>
    <p class="lede">Tender pages on this site are removed automatically the day
    after the closing date published on eTenders, so a link to a closed tender
    ends up here or on the &ldquo;page not found&rdquo; page.</p>
    <p>Closed or cancelled tenders, awards and re-advertisements are published on
    the National Treasury eTenders portal:
    <a href="https://www.etenders.gov.za/" rel="nofollow">www.etenders.gov.za</a>.</p>
    <h2>Find an open tender instead</h2>
    <ul>
      <li><a href="/tenders/index.html">All open South African government tenders</a></li>
      <li><a href="/tenders/closing-this-week.html">Tenders closing this week</a></li>
      <li><a href="/za-closing-soon.html">Tenders closing in the next 21 days</a></li>
    </ul>
""" + cta("Scoring map request: SA tender", "Bidding on a re-advertised tender?"),
        robots="noindex,follow")

    # --- manifest (read back next run for the collapse guard)
    files[f"{TENDERS_DIR}/manifest.json"] = json.dumps({
        "built_for": today.isoformat(),
        "open_tenders": len(open_t),
        "fresh_open": stats.get("fresh_open", len(open_t)),
        "tender_pages": min(len(open_t), MAX_TENDER_PAGES),
        "closing_this_week": len(this_week),
        "provinces": {p: len(by_prov[p]) for p in prov_order},
        "categories": {cat_names[k]: len(by_cat[k]) for k in cat_order},
    }, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
    return files


def lastmod_for(rel_path: str, records_by_path: dict, today: date) -> str:
    r = records_by_path.get(rel_path)
    if r:
        cands = [r["release_date"], r["open_date"]] + [d["published"] for d in r["documents"]]
        cands = [c for c in cands if c and c <= today.isoformat()]
        return max(cands) if cands else ""
    return today.isoformat()


def site_pages(root: Path) -> list[str]:
    """Indexable static pages outside tenders/ (skip noindex and 404)."""
    out = []
    for f in sorted(root.rglob("*.html")):
        rel = f.relative_to(root).as_posix()
        if rel.startswith((".", TENDERS_DIR + "/")) or "/." in rel or rel == "404.html":
            continue
        head = f.read_text(encoding="utf-8", errors="replace")[:4000].lower()
        if re.search(r'<meta[^>]+name=["\']robots["\'][^>]+noindex', head):
            continue
        out.append(rel)
    return out


def render_sitemap(root: Path, files: dict[str, str], records_by_path: dict,
                   today: date) -> str:
    urls = []
    for rel in site_pages(root):
        loc = SITE + "/" + ("" if rel == "index.html" else rel)
        urls.append((loc, ""))
    for rel in sorted(files):
        if not rel.endswith(".html") or rel.endswith("closed.html"):
            continue
        urls.append((SITE + "/" + rel, lastmod_for(rel, records_by_path, today)))
    lines = ['<?xml version="1.0" encoding="UTF-8"?>',
             '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
    for loc, lm in urls:
        lines.append(f"  <url><loc>{e(loc)}</loc>" + (f"<lastmod>{lm}</lastmod>" if lm else "") + "</url>")
    lines.append("</urlset>")
    return "\n".join(lines) + "\n"


def render_robots(root: Path) -> str:
    p = root / "robots.txt"
    text = p.read_text(encoding="utf-8") if p.exists() else "User-agent: *\nAllow: /\n"
    text = text.replace("\r\n", "\n")
    lines = [ln for ln in text.rstrip("\n").split("\n") if not ln.lower().startswith("sitemap:")]
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines) + f"\n\nSitemap: {SITE}/sitemap.xml\n"


# --------------------------------------------------------------------------
# writing

def write_outputs(root: Path, files: dict[str, str], extra: dict[str, str]) -> tuple[list[str], list[str]]:
    """Write changed files, delete stale tenders/ files. Returns (changed, removed)."""
    changed: list[str] = []
    for rel, content in sorted({**files, **extra}.items()):
        p = root / rel
        old = p.read_text(encoding="utf-8").replace("\r\n", "\n") if p.exists() else None
        if old == content:
            continue
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(content)
        changed.append(rel)
    removed: list[str] = []
    tdir = root / TENDERS_DIR
    for p in sorted(tdir.rglob("*")):
        if p.is_file():
            rel = p.relative_to(root).as_posix()
            if rel not in files:
                p.unlink()
                removed.append(rel)
    for d in sorted((x for x in tdir.rglob("*") if x.is_dir()), reverse=True):
        if not any(d.iterdir()):
            d.rmdir()
    return changed, removed


# --------------------------------------------------------------------------
# IndexNow

def find_key(root: Path) -> str | None:
    for p in sorted(root.glob("*.txt")):
        if re.fullmatch(r"[0-9a-f]{32}", p.stem) and p.read_text(encoding="utf-8").strip() == p.stem:
            return p.stem
    return None


def indexnow_ping(root: Path, urls: list[str], log=print) -> None:
    """POST changed URLs to IndexNow. Never raises."""
    try:
        urls = sorted(set(u for u in urls if u.startswith(SITE + "/")))[:INDEXNOW_MAX]
        if not urls:
            log("IndexNow: nothing to ping")
            return
        key = find_key(root)
        if not key:
            log("IndexNow: no key file found, skipping")
            return
        body = json.dumps({"host": HOST, "key": key,
                           "keyLocation": f"{SITE}/{key}.txt",
                           "urlList": urls}).encode("utf-8")
        req = urllib.request.Request(INDEXNOW_ENDPOINT, data=body, method="POST", headers={
            "Content-Type": "application/json; charset=utf-8", "User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=60) as resp:
            log(f"IndexNow: HTTP {resp.status} for {len(urls)} URLs")
    except urllib.error.HTTPError as exc:
        log(f"IndexNow: HTTP {exc.code} (ignored)")
    except Exception as exc:  # noqa: BLE001 - pinging must never fail the build
        log(f"IndexNow: failed ({type(exc).__name__}: {exc}) (ignored)")


def url_for_file(rel: str) -> str | None:
    if rel.endswith(".html"):
        if rel.endswith("closed.html"):
            return None
        return SITE + "/" + rel
    if rel == "sitemap.xml":
        return None
    return None


# --------------------------------------------------------------------------
# main

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Build the /tenders section from eTenders.")
    ap.add_argument("--today", help="Reference date YYYY-MM-DD (default: today's UTC date).")
    ap.add_argument("--root", default=str(ROOT), help="Repo root to write into.")
    ap.add_argument("--back-days", type=int, default=60)
    ap.add_argument("--forward-days", type=int, default=1)
    ap.add_argument("--max-requests", type=int, default=15000)
    ap.add_argument("--max-minutes", type=int, default=70)
    ap.add_argument("--save-json", help="Save the raw normalised fetch to this file.")
    ap.add_argument("--input-json", help="Skip the API and build from a --save-json file.")
    ap.add_argument("--no-ping", action="store_true", help="Do not ping IndexNow.")
    ap.add_argument("--changed-out", help="Write the changed/removed URL list here.")
    ap.add_argument("--ping-file", help="Only ping IndexNow with the URLs in this file, then exit.")
    args = ap.parse_args(argv)

    root = Path(args.root).resolve()
    log = lambda *a: print(*a, flush=True)  # noqa: E731

    if args.ping_file:
        urls = [u.strip() for u in Path(args.ping_file).read_text(encoding="utf-8").splitlines() if u.strip()]
        indexnow_ping(root, urls, log)
        return 0

    today = date.fromisoformat(args.today) if args.today else datetime.now(timezone.utc).date()
    log(f"[build_site] reference date {today}, root {root}")

    prev, manifest = load_previous(root)

    # ---- 1. fetch (no files touched)
    day_stats: dict = {}
    client = None
    try:
        if args.input_json:
            snap = json.loads(Path(args.input_json).read_text(encoding="utf-8"))
            records, day_stats = snap["records"], snap["day_stats"]
            fetched = snap["fetched"]
        else:
            client = Client(args.max_requests, args.max_minutes * 60)
            raw, day_stats = fetch_all(client, today, args.back_days, args.forward_days, log)
            fetched = len(raw)
            records = [n for n in (normalise(r) for r in raw) if n]
            if args.save_json:
                Path(args.save_json).write_text(json.dumps(
                    {"fetched": fetched, "records": records, "day_stats": day_stats},
                    ensure_ascii=False), encoding="utf-8")
    except FetchAbort as exc:
        log(f"ABORT: {exc}. Existing pages left untouched.")
        return 2

    unique = dedupe(records)
    open_now = [r for r in unique if is_open(r, today)]
    log(f"[build_site] releases fetched {fetched}, unique tenders {len(unique)}, open {len(open_now)}")
    if client:
        log(f"[build_site] requests {client.requests}, failed pages {client.failures}, codes {dict(client.http_codes)}")

    # ---- 2. sanity guards, on what the API returned THIS run
    fresh_open = len(open_now)
    if fresh_open < MIN_OPEN_TENDERS:
        log(f"ABORT: only {fresh_open} open tenders (< {MIN_OPEN_TENDERS}). Existing pages left untouched.")
        return 3
    got_total = sum(s["releases"] for s in day_stats.values())
    lost_total = sum(s["lost"] for s in day_stats.values())
    if got_total + lost_total and lost_total > MAX_LOST_RATIO * (got_total + lost_total):
        log(f"ABORT: {lost_total} records lost vs {got_total} fetched. Existing pages left untouched.")
        return 5

    # ---- 3. carry over previously published, still-open tenders whose
    #         advertise day lost records this run (poison/transient 5xx),
    #         or that were advertised before the fetch window
    have = {r["ocid"] for r in open_now}
    lossy_days = {d for d, s in day_stats.items() if s.get("lost")}
    carried = 0
    for ocid, r in sorted(prev.items()):
        if ocid in have or not is_open(r, today):
            continue
        rd = r.get("release_date") or ""
        if rd in lossy_days or rd not in day_stats:
            open_now.append(r)
            carried += 1
    if carried:
        log(f"[build_site] carried over {carried} still-open tenders from the previous run")

    # Collapse guard on the TOTAL after carry-over. Daily runs fetch a short
    # window and carry older open tenders forward from the published pages, so
    # comparing a 14-day fetch against a 60-day total would always trip.
    prev_total = int(manifest.get("open_tenders") or 0)
    if prev_total and len(open_now) < MIN_OPEN_RATIO * prev_total:
        log(f"ABORT: open tenders fell from {prev_total} to {len(open_now)}. Existing pages left untouched.")
        return 4

    # ---- 4. render in memory
    files = build(open_now, today, {"fresh_open": fresh_open})
    records_by_path = {tender_url(r).lstrip("/"): r for r in open_now}
    extra = {
        "sitemap.xml": render_sitemap(root, files, records_by_path, today),
        "robots.txt": render_robots(root),
    }

    # ---- 5. write
    changed, removed = write_outputs(root, files, extra)
    counts = Counter()
    for rel in files:
        if rel.endswith(".html"):
            counts[rel.split("/")[1] if rel.count("/") >= 2 else rel.split("/")[-1]] += 1
    sitemap_urls = extra["sitemap.xml"].count("<loc>")
    log(f"[build_site] pages: {dict(sorted(counts.items()))}; sitemap URLs {sitemap_urls}")
    log(f"[build_site] files changed {len(changed)}, removed {len(removed)}")

    urls = [u for u in (url_for_file(c) for c in changed) if u]
    # Removed pages are pinged too: IndexNow accepts URLs that now 404.
    urls += [SITE + "/" + r for r in removed if r.endswith(".html")]
    if args.changed_out:
        Path(args.changed_out).write_text("\n".join(sorted(set(urls))) + ("\n" if urls else ""), encoding="utf-8")
    if not args.no_ping:
        indexnow_ping(root, urls, log)
    return 0


if __name__ == "__main__":
    sys.exit(main())
