#!/usr/bin/env python3
"""Check the entries of `references.bib` against Crossref and a Zotero library.

An entry is matched to records that describe the same work: Crossref by its DOI, or by a
bibliographic search when it has none, and Zotero items by DOI or by title and first author. Its
fields are then compared with each record's: title, authors, year, venue (journal or book),
volume, issue and pages. An entry is `verified` when some record matches it and agrees on every
field both have, `mismatch` when a matched record disagrees on a field, and `unresolved` when no
record matches. Crossref responses are cached, so a rerun only asks for what is new.

Usage, from the repository root:

    python3 scripts/verify_bib.py --zotero ~/Zotero/zotero.sqlite     # full run
    python3 scripts/verify_bib.py --key chemla-2009a                    # one entry
    python3 scripts/verify_bib.py --no-search                           # DOIs only

The report is written to `.lake/build/bibcheck/report.json`, with a summary on standard output.
"""

import argparse
import concurrent.futures
import difflib
import hashlib
import html
import json
import re
import shutil
import sqlite3
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gen_bibliography_page import parse_bib, tex_text  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
BIB = ROOT / "references.bib"
OUT = ROOT / ".lake" / "build" / "bibcheck"
CACHE = OUT / "crossref"
UA = "linglib-bibcheck/1.0 (https://github.com/linglib-community/linglib)"
SELECT = "DOI,title,subtitle,author,editor,issued,published-print,published-online,container-title,volume,issue,page,type"


# ---------------------------------------------------------------- normalizing


def norm(s):
    """Lowercase ASCII words, for comparing text across sources: without TeX, HTML markup, or a
    leading chapter number (`40. Pronouns`, `II.—On Denoting`)."""
    s = re.sub(r"<[^>]+>", " ", html.unescape(html.unescape(s or "")))
    s = re.sub(r"^\s*(?:\d+|[IVXLC]+)\s*\.\s*[—–-]?\s*", "", s)
    s = unicodedata.normalize("NFKD", tex_text(s)).encode("ascii", "ignore").decode()
    return " ".join(re.sub(r"[^a-z0-9]+", " ", s.lower()).split())


def similar(a, b):
    a, b = norm(a), norm(b)
    if not a or not b:
        return 0.0
    if a == b or a.startswith(b + " ") or b.startswith(a + " "):
        return 1.0
    return difflib.SequenceMatcher(None, a, b).ratio()


def surnames(field):
    """Family names, in order, from a BibTeX name list."""
    out = []
    for n in re.split(r"\s+and\s+", field or ""):
        n = tex_text(n).strip()
        if not n or n == "others":
            continue
        last = n.split(",")[0] if "," in n else n.split()[-1]
        out.append(norm(last))
    return out


def same_surname(a, b):
    return a == b or a.endswith(" " + b) or b.endswith(" " + a) or a.replace(" ", "") == b.replace(" ", "")


def pages(s):
    """A page range as (first, last), without an article-number prefix (`2:1-31`); a single page
    `998-998` is `998`."""
    s = tex_text(s or "").replace("–", "-").replace("—", "-")
    s = re.sub(r"^\s*\d+\s*:\s*", "", s)
    ps = tuple(p.strip() for p in re.split(r"-+", s) if p.strip())
    return ps[:1] if len(ps) == 2 and ps[0] == ps[1] else ps


def pages_agree(a, b):
    """Two page ranges agree when equal, or when one source gives only the first page."""
    a, b = pages(a), pages(b)
    if a == b or not a or not b:
        return True
    if (len(a) == 1 or len(b) == 1) and a[0] == b[0]:
        return True
    return False


def years(*dates):
    out = set()
    for d in dates:
        if isinstance(d, dict):
            for parts in d.get("date-parts", []):
                if parts and parts[0]:
                    out.add(str(parts[0]))
        elif d:
            m = re.search(r"\b(1[5-9]\d\d|20\d\d)\b", str(d))
            if m:
                out.add(m.group(1))
    return out


# ---------------------------------------------------------------- Crossref


_lock = threading.Lock()
_last = [0.0]


def fetch(url):
    """A Crossref response, from the cache or the API, at most a few requests a second."""
    path = CACHE / (hashlib.sha1(url.encode()).hexdigest() + ".json")
    if path.exists():
        return json.loads(path.read_text())
    for attempt in range(4):
        with _lock:
            wait = _last[0] + 0.12 - time.time()
            if wait > 0:
                time.sleep(wait)
            _last[0] = time.time()
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=30) as r:
                data = json.loads(r.read())
            break
        except urllib.error.HTTPError as e:
            if e.code == 404:
                data = None
                break
            time.sleep(2 ** attempt * 2)
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            time.sleep(2 ** attempt * 2)
    else:
        return {"error": "unreachable"}
    path.write_text(json.dumps(data))
    return data


def crossref_doi(doi):
    data = fetch("https://api.crossref.org/works/" + urllib.parse.quote(doi, safe="/"))
    return data.get("message") if isinstance(data, dict) and "message" in data else None


def datacite_doi(doi):
    """A DataCite record (Zenodo, OSF, lingbuzz mirrors and other repositories), as Crossref's."""
    data = fetch("https://api.datacite.org/dois/" + urllib.parse.quote(doi, safe=""))
    if not isinstance(data, dict) or "data" not in data:
        return None
    a = data["data"]["attributes"]
    return {
        "DOI": a.get("doi", doi), "type": (a.get("types") or {}).get("resourceTypeGeneral", ""),
        "title": [t["title"] for t in a.get("titles", [])[:1]],
        "author": [{"family": c.get("familyName") or c.get("name", "")} for c in a.get("creators", [])],
        "issued": {"date-parts": [[a.get("publicationYear")]]},
        "container-title": [(a.get("container") or {}).get("title", "")],
    }


def doi_exists(doi):
    """Whether doi.org resolves a DOI, whatever its registration agency."""
    data = fetch("https://doi.org/api/handles/" + urllib.parse.quote(doi, safe="/"))
    return isinstance(data, dict) and data.get("responseCode") == 1


# The Crossref record types that can describe a work of each BibTeX type.
COMPATIBLE = {
    "article": {"journal-article"},
    "inproceedings": {"proceedings-article", "book-chapter", "journal-article"},
    "incollection": {"book-chapter", "book-part", "book-section", "reference-entry"},
    "inbook": {"book-chapter", "book-part", "book-section"},
    "book": {"book", "monograph", "edited-book", "reference-book", "book-set"},
    "phdthesis": {"dissertation"},
    "mastersthesis": {"dissertation"},
    "techreport": {"report", "report-component"},
}


def crossref_search(f, kind):
    first = (surnames(f.get("author") or f.get("editor")) or [""])[0]
    q = " ".join([tex_text(f.get("title", "")), first, f.get("year", "")])
    url = ("https://api.crossref.org/works?rows=5&select=" + SELECT + "&query.bibliographic="
           + urllib.parse.quote(q))
    data = fetch(url)
    if not isinstance(data, dict) or "message" not in data:
        return None
    best = None
    for item in data["message"].get("items", []):
        if item.get("type") not in COMPATIBLE.get(kind, set()):
            continue
        title = " ".join(item.get("title", []))
        sub = " ".join(item.get("subtitle", []))
        score = max(similar(f.get("title", ""), title), similar(f.get("title", ""), title + " " + sub))
        names = [norm(a.get("family", "")) for a in item.get("author", []) + item.get("editor", [])]
        if score >= 0.93 and (not first or any(same_surname(first, n) for n in names)):
            if not best or score > best[0]:
                best = (score, item)
    return best[1] if best else None


def from_crossref(m):
    title = " ".join(m.get("title", []))
    sub = " ".join(m.get("subtitle", []))
    return {
        "source": "crossref", "id": m.get("DOI", ""), "type": m.get("type", ""),
        "title": title, "subtitle": sub,
        "authors": [norm(a.get("family", a.get("name", ""))) for a in m.get("author", [])],
        "editors": [norm(a.get("family", a.get("name", ""))) for a in m.get("editor", [])],
        "years": sorted(years(m.get("issued"), m.get("published-print"), m.get("published-online"))),
        "venue": " ".join(m.get("container-title", [])), "volume": m.get("volume", ""),
        "issue": m.get("issue", ""), "pages": m.get("page", ""), "doi": m.get("DOI", "").lower(),
    }


# ---------------------------------------------------------------- Zotero


def zotero_items(path):
    """The regular items of a Zotero library, read from a copy of its database, since Zotero
    locks the original while it runs; the copy is deleted once read."""
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "zotero.sqlite"
        shutil.copy(path, copy)
        return read_zotero(copy)


def read_zotero(path):
    db = sqlite3.connect(path)
    kinds = dict(db.execute(
        "select i.itemID, t.typeName from items i join itemTypes t using(itemTypeID) "
        "where t.typeName not in ('attachment','note','annotation') "
        "and i.itemID not in (select itemID from deletedItems)"))
    fields = {}
    for item, name, value in db.execute(
            "select d.itemID, f.fieldName, v.value from itemData d join fields f using(fieldID) "
            "join itemDataValues v using(valueID)"):
        if item in kinds:
            fields.setdefault(item, {})[name] = value
    creators = {}
    for item, last, kind in db.execute(
            "select c.itemID, cr.lastName, t.creatorType from itemCreators c "
            "join creators cr using(creatorID) join creatorTypes t using(creatorTypeID) "
            "order by c.itemID, c.orderIndex"):
        if item in kinds:
            creators.setdefault(item, []).append((kind, last))
    pdfs = {p for (p,) in db.execute(
        "select parentItemID from itemAttachments where contentType = 'application/pdf'")}
    keys = dict(db.execute("select itemID, key from items"))
    out = []
    for item, kind in kinds.items():
        f = fields.get(item, {})
        cs = creators.get(item, [])
        out.append({
            "source": "zotero", "id": keys[item], "type": kind, "title": f.get("title", ""),
            "subtitle": "",
            "authors": [norm(l) for k, l in cs if k == "author"],
            "editors": [norm(l) for k, l in cs if k in ("editor", "seriesEditor")],
            "years": sorted(years(f.get("date"))),
            "venue": f.get("publicationTitle") or f.get("bookTitle") or f.get("proceedingsTitle", ""),
            "volume": f.get("volume", ""), "issue": f.get("issue", ""), "pages": f.get("pages", ""),
            "doi": f.get("DOI", "").lower(), "pdf": item in pdfs,
        })
    db.close()
    return out


class Zotero:
    """A Zotero library, matched by DOI, or by title and first author: the titles are the same,
    one begins with the other (a subtitle one source leaves out), or they are nearly the same."""

    def __init__(self, items):
        self.by_doi = {z["doi"]: z for z in items if z["doi"]}
        self.by_head = {}
        for z in items:
            self.by_head.setdefault(" ".join(norm(z["title"]).split()[:3]), []).append(z)

    def match(self, f):
        doi = f.get("doi", "").lower()
        if doi and doi in self.by_doi:
            return self.by_doi[doi], "doi"
        title = norm(f.get("title", ""))
        first = (surnames(f.get("author") or f.get("editor")) or [""])[0]
        best = None
        for z in self.by_head.get(" ".join(title.split()[:3]), []):
            if first and not any(same_surname(first, n) for n in z["authors"] + z["editors"]):
                continue
            score = similar(title, z["title"])
            if score >= 0.9 and (not best or score > best[0]):
                best = (score, z)
        return (best[1], "title") if best else (None, None)


# ---------------------------------------------------------------- comparing


def compare(kind, f, rec):
    """The fields on which an entry and a record disagree, each with both values."""
    diffs = {}
    bib_title = f.get("title", "")
    if rec["title"]:
        full = rec["title"] + (" " + rec["subtitle"] if rec["subtitle"] else "")
        if max(similar(bib_title, rec["title"]), similar(bib_title, full)) < 0.9:
            diffs["title"] = [tex_text(bib_title), full]
    names = surnames(f.get("author")) if f.get("author") else surnames(f.get("editor"))
    theirs = rec["authors"] if f.get("author") else (rec["editors"] or rec["authors"])
    if names and theirs:
        if len(names) != len(theirs) or not all(same_surname(a, b) for a, b in zip(names, theirs)):
            diffs["authors"] = [names, theirs]
    if f.get("year") and rec["years"] and f["year"] not in rec["years"]:
        diffs["year"] = [f["year"], rec["years"]]
    venue = f.get("journal") if kind == "article" else f.get("booktitle")
    if venue and rec["venue"] and similar(venue, rec["venue"]) < 0.8:
        diffs["venue"] = [tex_text(venue), rec["venue"]]
    for name, bib_name in (("volume", "volume"), ("issue", "number")):
        if f.get(bib_name) and rec[name] and norm(f[bib_name]) != norm(rec[name]):
            diffs[bib_name] = [f[bib_name], rec[name]]
    if f.get("pages") and rec["pages"] and not pages_agree(f["pages"], rec["pages"]):
        diffs["pages"] = [f["pages"], rec["pages"]]
    return diffs


def check(entry, zotero, search):
    kind, key, f = entry
    records = []
    doi = f.get("doi", "").strip().replace("\\_", "_")
    if doi:
        m = crossref_doi(doi)
        source = "crossref"
        if not m:
            m, source = datacite_doi(doi), "datacite"
        if m:
            records.append(dict(from_crossref(m), source=source, matched="doi"))
        elif not doi_exists(doi):
            records.append({"source": "doi.org", "id": doi, "matched": "doi", "missing": True})
    if zotero:
        z, how = zotero.match(f)
        if z:
            records.append(dict(z, matched=how))
    if search and not doi and kind not in ("misc", "unpublished") and f.get("title"):
        m = crossref_search(f, kind)
        if m:
            records.append(dict(from_crossref(m), matched="search"))
    result = {"key": key, "type": kind, "validated": f.get("validated", ""), "doi": doi,
              "title": tex_text(f.get("title", "")), "author": tex_text(f.get("author", "")),
              "year": f.get("year", ""), "records": []}
    for rec in records:
        if rec.get("missing"):
            result["records"].append({"source": "doi.org", "id": rec["id"], "matched": "doi",
                                      "error": "DOI does not resolve"})
            continue
        result["records"].append({"source": rec["source"], "id": rec["id"], "matched": rec["matched"],
                                  "pdf": rec.get("pdf"), "doi": rec.get("doi", ""),
                                  "diffs": compare(kind, f, rec)})
    good = [r for r in result["records"] if "diffs" in r]
    if any(r.get("error") for r in result["records"]):
        result["status"] = "bad-doi"
    elif not good:
        result["status"] = "unresolved"
    elif any(not r["diffs"] for r in good) and all(not r["diffs"] for r in good if r["matched"] == "doi"):
        result["status"] = "verified"
    else:
        result["status"] = "mismatch"
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--zotero", type=Path, help="a Zotero database, zotero.sqlite")
    ap.add_argument("--key", action="append", help="check only these entries")
    ap.add_argument("--no-search", action="store_true", help="skip Crossref searches")
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()

    CACHE.mkdir(parents=True, exist_ok=True)
    entries = parse_bib(BIB.read_text(encoding="utf-8"))
    if args.key:
        entries = [e for e in entries if e[1] in args.key]
    zotero = Zotero(zotero_items(args.zotero.expanduser())) if args.zotero else None
    results, done = [], 0
    with concurrent.futures.ThreadPoolExecutor(args.workers) as pool:
        for r in pool.map(lambda e: check(e, zotero, not args.no_search), entries):
            results.append(r)
            done += 1
            if done % 200 == 0:
                print(f"{done}/{len(entries)}", file=sys.stderr, flush=True)
    (OUT / "report.json").write_text(json.dumps(results, indent=1, ensure_ascii=False))
    counts = {}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    fields = {}
    for r in results:
        if r["status"] == "mismatch":
            for rec in r["records"]:
                for k in rec.get("diffs", {}):
                    fields[k] = fields.get(k, 0) + 1
    print(json.dumps({"entries": len(results), "status": counts, "mismatched fields": fields}))


if __name__ == "__main__":
    main()
