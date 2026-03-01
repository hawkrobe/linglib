#!/usr/bin/env python3
"""Verify references.bib entries against the CrossRef API.

CrossRef is the authoritative DOI registry and has richer metadata than
Semantic Scholar for catching journal name, volume, pages, and year
mismatches — the most common hallucination types in this project.

For entries WITH a DOI: queries CrossRef and compares title, year,
  journal/container-title, volume, issue, and pages.
For entries WITHOUT a DOI: searches CrossRef by title to suggest DOIs.

Uses the CrossRef "polite pool" for better rate limits (50 req/sec vs 1).

Usage:
    python blog/scripts/verify_crossref.py              # full run
    python blog/scripts/verify_crossref.py --doi-only   # skip entries without DOIs
    python blog/scripts/verify_crossref.py --key foo    # check one entry by key
"""

import json
import re
import sys
import time
import urllib.request
import urllib.error
import urllib.parse
from pathlib import Path

BIB_PATH = Path(__file__).resolve().parent.parent / "data" / "references.bib"

# CrossRef polite pool: include contact email for higher rate limits
HEADERS = {
    "User-Agent": "linglib-crossref-checker/1.0 (mailto:linglib@example.com)",
}
RATE_LIMIT = 0.2  # seconds between requests (polite pool allows ~50/sec)
MAX_RETRIES = 3

# Entry types where journal/container-title comparison makes sense
VENUE_TYPES = {"article", "inproceedings", "incollection"}


# ---------------------------------------------------------------------------
# BibTeX parser (shared pattern with other scripts)
# ---------------------------------------------------------------------------

def parse_bib(path: Path) -> list[dict]:
    text = path.read_text(encoding="utf-8")
    entries = []
    for m in re.finditer(r"@(\w+)\s*\{([^,]+),\s*(.*?)\n\}", text, re.DOTALL):
        key = m.group(2).strip()
        body = m.group(3)
        fields = {"_key": key, "_type": m.group(1).lower()}
        for fm in re.finditer(
            r"(\w[\w-]*)\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}", body
        ):
            fields[fm.group(1).lower()] = fm.group(2).strip()
        entries.append(fields)
    return entries


def clean_latex(s: str) -> str:
    """Strip BibTeX braces and common LaTeX commands."""
    s = re.sub(r"\{\\['\"`~^v]?\{?(\w)\}?\}", r"\1", s)  # accents
    s = re.sub(r"\\textasciitilde", "~", s)
    s = re.sub(r"\$[^$]*\$", "", s)  # math mode
    s = re.sub(r"[{}\\]", "", s)
    return s.strip()


def normalize(s: str) -> str:
    """Lowercase, strip punctuation, collapse whitespace."""
    s = clean_latex(s)
    s = re.sub(r"[^a-z0-9\s]", "", s.lower())
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------------------
# CrossRef API
# ---------------------------------------------------------------------------

def crossref_get(url: str) -> dict | None:
    for attempt in range(MAX_RETRIES):
        try:
            req = urllib.request.Request(url, headers=HEADERS)
            with urllib.request.urlopen(req, timeout=20) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < MAX_RETRIES - 1:
                wait = 2 ** (attempt + 1)
                print(f"  (429, retrying in {wait}s) ", end="", flush=True)
                time.sleep(wait)
                continue
            if e.code == 404:
                return None
            return {"_error": f"HTTP {e.code}"}
        except Exception as e:
            if attempt < MAX_RETRIES - 1:
                time.sleep(1)
                continue
            return {"_error": str(e)[:100]}
    return {"_error": "max retries"}


def fetch_by_doi(doi: str) -> dict | None:
    url = f"https://api.crossref.org/works/{urllib.parse.quote(doi, safe='')}"
    data = crossref_get(url)
    if data is None or (isinstance(data, dict) and "_error" in data):
        return data
    return data.get("message", {})


def search_by_title(title: str) -> list[dict]:
    q = normalize(title)[:200]
    params = urllib.parse.urlencode({"query.bibliographic": q, "rows": 3})
    url = f"https://api.crossref.org/works?{params}"
    data = crossref_get(url)
    if data is None or (isinstance(data, dict) and "_error" in data):
        return [data] if data else []
    return data.get("message", {}).get("items", [])


# ---------------------------------------------------------------------------
# Comparison logic
# ---------------------------------------------------------------------------

def cr_title(item: dict) -> str:
    """Extract title from CrossRef item."""
    titles = item.get("title", [])
    return titles[0] if titles else ""


def cr_container(item: dict) -> str:
    """Extract container/journal title from CrossRef item."""
    containers = item.get("container-title", [])
    return containers[0] if containers else ""


def cr_year(item: dict) -> str:
    """Extract publication year from CrossRef item."""
    # Prefer published-print, then published-online, then issued
    for field in ("published-print", "published-online", "issued"):
        date_parts = item.get(field, {}).get("date-parts", [[]])
        if date_parts and date_parts[0]:
            return str(date_parts[0][0])
    return ""


def cr_pages(item: dict) -> str:
    return item.get("page", "")


def cr_volume(item: dict) -> str:
    return item.get("volume", "")


def cr_issue(item: dict) -> str:
    return item.get("issue", "")


def cr_authors(item: dict) -> list[str]:
    """Extract author last names from CrossRef item."""
    authors = item.get("author", [])
    return [a.get("family", "") for a in authors if a.get("family")]


def title_similarity(a: str, b: str) -> float:
    """Word overlap similarity between two normalized strings."""
    wa = set(normalize(a).split())
    wb = set(normalize(b).split())
    if not wa or not wb:
        return 0.0
    return len(wa & wb) / max(len(wa), len(wb))


def normalize_pages(p: str) -> str:
    """Normalize page ranges: strip spaces, normalize dashes, deduplicate."""
    p = clean_latex(p)
    p = re.sub(r"\s+", "", p)
    p = re.sub(r"[-–—]+", "-", p)
    p = p.lower()
    # Normalize "998-998" → "998" (single-page articles)
    parts = p.split("-")
    if len(parts) == 2 and parts[0] == parts[1]:
        p = parts[0]
    return p


def normalize_journal(j: str) -> str:
    """Normalize journal name for comparison."""
    j = clean_latex(j)
    # Common abbreviation expansions
    j = j.replace("&", "and")
    return re.sub(r"\s+", " ", j).strip().lower()


def compare_entry(entry: dict, cr: dict) -> list[tuple[str, str, str]]:
    """Compare bib entry with CrossRef data.

    Returns list of (field, bib_value, crossref_value) tuples for mismatches.
    """
    issues = []

    # Title
    bib_title = entry.get("title", "")
    xr_title = cr_title(cr)
    sim = title_similarity(bib_title, xr_title)
    if sim < 0.7 and bib_title and xr_title:
        issues.append(("title", clean_latex(bib_title), xr_title))

    # Year
    bib_year = entry.get("year", "")
    xr_year = cr_year(cr)
    if bib_year and xr_year and bib_year != xr_year:
        issues.append(("year", bib_year, xr_year))

    # Journal / container title
    etype = entry.get("_type", "")
    if etype in VENUE_TYPES:
        bib_journal = entry.get("journal", entry.get("booktitle", ""))
        xr_journal = cr_container(cr)
        if bib_journal and xr_journal:
            bn = normalize_journal(bib_journal)
            xn = normalize_journal(xr_journal)
            # Check if one is a substring of the other (handles abbreviations)
            if bn not in xn and xn not in bn:
                # Word overlap check
                bw = set(bn.split())
                xw = set(xn.split())
                overlap = len(bw & xw) / max(len(bw), len(xw), 1)
                if overlap < 0.5:
                    issues.append((
                        "journal",
                        clean_latex(bib_journal),
                        xr_journal,
                    ))

    # Volume
    bib_vol = entry.get("volume", "")
    xr_vol = cr_volume(cr)
    if bib_vol and xr_vol and bib_vol != xr_vol:
        issues.append(("volume", bib_vol, xr_vol))

    # Issue/number
    bib_num = entry.get("number", "")
    xr_num = cr_issue(cr)
    if bib_num and xr_num and bib_num != xr_num:
        issues.append(("issue", bib_num, xr_num))

    # Pages
    bib_pages = normalize_pages(entry.get("pages", ""))
    xr_pages = normalize_pages(cr_pages(cr))
    if bib_pages and xr_pages and bib_pages != xr_pages:
        issues.append(("pages", entry.get("pages", ""), cr_pages(cr)))

    # Authors (last name check)
    bib_author_str = clean_latex(entry.get("author", ""))
    bib_lastnames = [
        a.split(",")[0].strip().lower()
        for a in bib_author_str.split(" and ")
        if a.strip()
    ]
    xr_lastnames = [n.lower() for n in cr_authors(cr)]
    if bib_lastnames and xr_lastnames:
        bib_set = set(bib_lastnames)
        xr_set = set(xr_lastnames)
        if bib_set and xr_set:
            overlap = len(bib_set & xr_set) / max(len(bib_set), len(xr_set))
            if overlap < 0.5:
                issues.append((
                    "authors",
                    ", ".join(bib_lastnames),
                    ", ".join(xr_lastnames),
                ))

    return issues


# ---------------------------------------------------------------------------
# Output formatting
# ---------------------------------------------------------------------------

def severity(field: str) -> str:
    """Assign severity level to a field mismatch."""
    if field in ("title", "journal", "authors"):
        return "HIGH"
    if field in ("year", "volume"):
        return "MEDIUM"
    return "LOW"


def format_issues(issues: list[tuple[str, str, str]]) -> list[str]:
    lines = []
    for field, bib_val, xr_val in issues:
        sev = severity(field)
        lines.append(f"  [{sev:6s}] {field}:")
        lines.append(f"           bib:      {bib_val}")
        lines.append(f"           crossref: {xr_val}")
    return lines


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    doi_only = "--doi-only" in sys.argv
    key_filter = None
    if "--key" in sys.argv:
        idx = sys.argv.index("--key")
        if idx + 1 < len(sys.argv):
            key_filter = sys.argv[idx + 1]

    entries = parse_bib(BIB_PATH)
    print(f"Loaded {len(entries)} entries from {BIB_PATH}")

    if key_filter:
        entries = [e for e in entries if e["_key"] == key_filter]
        if not entries:
            print(f"No entry found with key '{key_filter}'")
            sys.exit(1)

    with_doi = [e for e in entries if e.get("doi")]
    without_doi = [e for e in entries if not e.get("doi")]

    print(f"  {len(with_doi)} with DOI, {len(without_doi)} without DOI\n")

    # ── Phase 1: verify entries with DOIs ──

    print("=" * 72)
    print("PHASE 1: Verifying entries with DOIs against CrossRef")
    print("=" * 72 + "\n")

    verified_ok = []
    mismatches = []
    doi_errors = []

    for i, entry in enumerate(with_doi):
        key = entry["_key"]
        doi = entry["doi"]
        print(f"[{i+1:3d}/{len(with_doi)}] {key:45s} ", end="", flush=True)

        cr = fetch_by_doi(doi)
        time.sleep(RATE_LIMIT)

        if cr is None:
            print("NOT FOUND (invalid DOI?)")
            doi_errors.append((key, "DOI not found in CrossRef"))
            continue
        if isinstance(cr, dict) and "_error" in cr:
            print(f"ERROR: {cr['_error']}")
            doi_errors.append((key, cr["_error"]))
            continue

        issues = compare_entry(entry, cr)
        if issues:
            high = sum(1 for f, _, _ in issues if severity(f) == "HIGH")
            med = sum(1 for f, _, _ in issues if severity(f) == "MEDIUM")
            low = sum(1 for f, _, _ in issues if severity(f) == "LOW")
            parts = []
            if high:
                parts.append(f"{high} HIGH")
            if med:
                parts.append(f"{med} MEDIUM")
            if low:
                parts.append(f"{low} LOW")
            print(f"MISMATCH ({', '.join(parts)})")
            mismatches.append((key, issues))
        else:
            print("OK")
            verified_ok.append(key)

    print(f"\nPhase 1: {len(verified_ok)}/{len(with_doi)} verified OK, "
          f"{len(mismatches)} mismatches, {len(doi_errors)} errors\n")

    # ── Phase 2: search for DOIs for entries without them ──

    suggested_dois = []
    no_match = []
    search_errors = []

    if not doi_only and without_doi:
        print("=" * 72)
        print("PHASE 2: Searching CrossRef for entries without DOIs")
        print("=" * 72 + "\n")

        for i, entry in enumerate(without_doi):
            key = entry["_key"]
            title = entry.get("title", "")
            print(f"[{i+1:3d}/{len(without_doi)}] {key:45s} ", end="", flush=True)

            results = search_by_title(title)
            time.sleep(RATE_LIMIT)

            if not results:
                print("NO RESULTS")
                no_match.append(key)
                continue
            if isinstance(results[0], dict) and "_error" in results[0]:
                print(f"ERROR: {results[0]['_error']}")
                search_errors.append((key, results[0]["_error"]))
                continue

            # Find best title match
            best = None
            best_sim = 0.0
            for item in results:
                sim = title_similarity(title, cr_title(item))
                if sim > best_sim:
                    best_sim = sim
                    best = item

            if best is None or best_sim < 0.5:
                cr_titles = [cr_title(r) for r in results[:2]]
                print(f"NO GOOD MATCH (best: '{cr_titles[0][:50]}...' sim={best_sim:.2f})")
                no_match.append(key)
                continue

            xr_doi = best.get("DOI", "")
            if xr_doi:
                issues = compare_entry(entry, best)
                issue_note = ""
                if issues:
                    fields = [f for f, _, _ in issues]
                    issue_note = f" (also check: {', '.join(fields)})"
                print(f"FOUND DOI: {xr_doi}{issue_note}")
                suggested_dois.append((key, xr_doi, issues))
            else:
                print(f"MATCH (sim={best_sim:.2f}) but no DOI available")
                no_match.append(key)

        print(f"\nPhase 2: {len(suggested_dois)} DOIs found, "
              f"{len(no_match)} no match, {len(search_errors)} errors\n")

    # ── Summary report ──

    print("=" * 72)
    print("SUMMARY REPORT")
    print("=" * 72)

    print(f"\n  Entries verified OK:         {len(verified_ok)}/{len(with_doi)}")
    print(f"  Entries with mismatches:     {len(mismatches)}")
    print(f"  DOI lookup errors:           {len(doi_errors)}")
    if not doi_only:
        print(f"  Suggested new DOIs:          {len(suggested_dois)}")
        print(f"  No DOI available:            {len(no_match)}")

    if mismatches:
        # Sort by severity: HIGH first
        mismatches.sort(
            key=lambda x: -sum(1 for f, _, _ in x[1] if severity(f) == "HIGH")
        )
        print(f"\n{'─' * 72}")
        print("MISMATCHES (sorted by severity)")
        print(f"{'─' * 72}")
        for key, issues in mismatches:
            print(f"\n  {key}:")
            for line in format_issues(issues):
                print(f"  {line}")

    if doi_errors:
        print(f"\n{'─' * 72}")
        print("DOI ERRORS")
        print(f"{'─' * 72}")
        for key, err in doi_errors:
            print(f"  {key}: {err}")

    if suggested_dois:
        print(f"\n{'─' * 72}")
        print("SUGGESTED DOIs (add to references.bib)")
        print(f"{'─' * 72}")
        for key, doi, issues in suggested_dois:
            print(f"  {key}:")
            print(f"    doi = {{{doi}}}")
            if issues:
                for line in format_issues(issues):
                    print(f"  {line}")

    # Exit code: nonzero if any HIGH-severity mismatches
    high_count = sum(
        1 for _, issues in mismatches
        for f, _, _ in issues if severity(f) == "HIGH"
    )
    if high_count:
        print(f"\n{high_count} HIGH-severity mismatch(es) found.")
        sys.exit(1)
    else:
        print("\nNo HIGH-severity mismatches.")
        sys.exit(0)


if __name__ == "__main__":
    main()
