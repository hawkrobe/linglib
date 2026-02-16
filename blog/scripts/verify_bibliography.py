#!/usr/bin/env python3
"""Verify references.bib entries against the Semantic Scholar API.

For entries with DOIs: looks up the DOI and compares metadata.
For entries without DOIs: searches by title and reports potential matches with DOIs.

Usage:
    python blog/scripts/verify_bibliography.py

Requires: internet access (queries api.semanticscholar.org)
No external dependencies — uses only stdlib.
"""

import json
import re
import sys
import time
import urllib.request
import urllib.parse
import urllib.error
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIB_PATH = ROOT / "data" / "references.bib"

S2_API = "https://api.semanticscholar.org/graph/v1/paper"
FIELDS = "title,authors,year,venue,externalIds"
BASE_DELAY = 3.5  # base seconds between requests
MAX_RETRIES = 4


def parse_bib(path: Path) -> list[dict]:
    """Minimal BibTeX parser."""
    text = path.read_text(encoding="utf-8")
    entries = []
    for m in re.finditer(
        r"@(\w+)\s*\{([^,]+),\s*(.*?)\n\}", text, re.DOTALL
    ):
        entry_type = m.group(1).lower()
        key = m.group(2).strip()
        body = m.group(3)
        fields = {"_type": entry_type, "_key": key}
        for fm in re.finditer(
            r"(\w[\w-]*)\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}", body
        ):
            fname = fm.group(1).lower()
            fval = fm.group(2).strip()
            if fval.startswith("{") and fval.endswith("}"):
                fval = fval[1:-1]
            fields[fname] = fval
        entries.append(fields)
    return entries


def _fetch_url(url: str) -> dict | list | None:
    """Fetch a URL with retry and exponential backoff for 429s."""
    for attempt in range(MAX_RETRIES):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "linglib-bibcheck/1.0"})
            with urllib.request.urlopen(req, timeout=15) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            if e.code == 429:
                wait = BASE_DELAY * (2 ** attempt)
                print(f"(429, waiting {wait:.0f}s) ", end="", flush=True)
                time.sleep(wait)
                continue
            return {"_error": f"HTTP {e.code}: {e.reason}"}
        except (urllib.error.URLError, json.JSONDecodeError) as e:
            return {"_error": str(e)}
    return {"_error": "Rate limited after max retries"}


def fetch_by_doi(doi: str) -> dict | None:
    """Fetch paper metadata from Semantic Scholar by DOI."""
    url = f"{S2_API}/DOI:{urllib.parse.quote(doi, safe='')}?fields={FIELDS}"
    return _fetch_url(url)


def search_by_title(title: str) -> list[dict]:
    """Search Semantic Scholar by title."""
    clean = re.sub(r"\{\\['\"]?\w+\}", "", title)
    clean = re.sub(r"[{}]", "", clean)
    clean = clean.strip()

    params = urllib.parse.urlencode({
        "query": clean,
        "limit": 3,
        "fields": FIELDS,
    })
    url = f"{S2_API}/search?{params}"
    result = _fetch_url(url)
    if isinstance(result, dict):
        if "_error" in result:
            return [result]
        return result.get("data", [])
    return []


def normalize_title(t: str) -> str:
    """Normalize title for comparison."""
    t = re.sub(r"[{}\\'\"]", "", t)
    t = re.sub(r"\s+", " ", t).strip().lower()
    return t


def compare_entry(entry: dict, s2: dict) -> list[str]:
    """Compare bib entry with Semantic Scholar data. Return list of discrepancies."""
    issues = []

    bib_title = normalize_title(entry.get("title", ""))
    s2_title = normalize_title(s2.get("title", ""))
    if bib_title and s2_title:
        if bib_title not in s2_title and s2_title not in bib_title:
            bib_words = set(bib_title.split())
            s2_words = set(s2_title.split())
            overlap = len(bib_words & s2_words) / max(len(bib_words), len(s2_words), 1)
            if overlap < 0.7:
                issues.append(f"  TITLE MISMATCH: bib='{entry.get('title', '')}' vs s2='{s2.get('title', '')}'")

    bib_year = entry.get("year", "")
    s2_year = str(s2.get("year", ""))
    if bib_year and s2_year and bib_year != s2_year:
        issues.append(f"  YEAR MISMATCH: bib={bib_year} vs s2={s2_year}")

    ext_ids = s2.get("externalIds", {}) or {}
    s2_doi = ext_ids.get("DOI", "")
    bib_doi = entry.get("doi", "")
    if bib_doi and s2_doi and bib_doi.lower() != s2_doi.lower():
        issues.append(f"  DOI MISMATCH: bib={bib_doi} vs s2={s2_doi}")

    if not bib_doi and s2_doi:
        issues.append(f"  MISSING DOI: could add doi = {{{s2_doi}}}")

    return issues


def main():
    entries = parse_bib(BIB_PATH)
    print(f"Loaded {len(entries)} entries from {BIB_PATH}\n")

    with_doi = [e for e in entries if e.get("doi")]
    without_doi = [e for e in entries if not e.get("doi")]

    print(f"Entries with DOI: {len(with_doi)}")
    print(f"Entries without DOI: {len(without_doi)}")
    print(f"\n{'='*70}")
    print("PHASE 1: Verifying entries with DOIs")
    print(f"{'='*70}\n")

    doi_issues = []
    doi_ok = 0
    for i, entry in enumerate(with_doi):
        key = entry["_key"]
        doi = entry["doi"]
        print(f"[{i+1}/{len(with_doi)}] {key} (DOI: {doi}) ... ", end="", flush=True)

        result = fetch_by_doi(doi)
        time.sleep(BASE_DELAY)

        if result is None:
            print("NOT FOUND")
            doi_issues.append((key, ["  DOI NOT FOUND in Semantic Scholar"]))
            continue

        if "_error" in result:
            err = result['_error']
            if "404" in err:
                print("NOT IN S2 (DOI valid but not indexed)")
                doi_issues.append((key, [f"  NOT IN S2 (may still be valid): {err}"]))
            else:
                print(f"ERROR: {err}")
                doi_issues.append((key, [f"  API ERROR: {err}"]))
            continue

        issues = compare_entry(entry, result)
        if issues:
            print("ISSUES FOUND")
            doi_issues.append((key, issues))
        else:
            print("OK")
            doi_ok += 1

    print(f"\nPhase 1 complete: {doi_ok}/{len(with_doi)} verified OK")

    print(f"\n{'='*70}")
    print("PHASE 2: Searching for entries without DOIs")
    print(f"{'='*70}\n")

    search_results = []
    search_ok = 0
    for i, entry in enumerate(without_doi):
        key = entry["_key"]
        title = entry.get("title", "")
        print(f"[{i+1}/{len(without_doi)}] {key} ... ", end="", flush=True)

        results = search_by_title(title)
        time.sleep(BASE_DELAY)

        if not results:
            print("NO RESULTS")
            search_results.append((key, ["  No results found on Semantic Scholar"]))
            continue

        if results and "_error" in results[0]:
            print(f"ERROR: {results[0]['_error']}")
            search_results.append((key, [f"  API ERROR: {results[0]['_error']}"]))
            continue

        best = results[0]
        issues = compare_entry(entry, best)

        ext_ids = best.get("externalIds", {}) or {}
        s2_doi = ext_ids.get("DOI", "")
        s2_title = best.get("title", "")

        bib_title_norm = normalize_title(entry.get("title", ""))
        s2_title_norm = normalize_title(s2_title)

        bib_words = set(bib_title_norm.split())
        s2_words = set(s2_title_norm.split())
        overlap = len(bib_words & s2_words) / max(len(bib_words), len(s2_words), 1)

        if overlap > 0.6:
            if s2_doi:
                print(f"FOUND DOI: {s2_doi}")
                issues.append(f"  SUGGESTED DOI: {s2_doi}")
            else:
                print("OK (no DOI available)")
                search_ok += 1
            if issues:
                search_results.append((key, issues))
        else:
            print(f"NO GOOD MATCH (best: '{s2_title}')")
            search_results.append((key, [f"  Best S2 match: '{s2_title}' (low overlap)"]))

    print(f"\nPhase 2 complete: {search_ok}/{len(without_doi)} verified OK (no DOI available)")

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}\n")

    # Filter out pure API errors from real issues
    real_doi_issues = [(k, iss) for k, iss in doi_issues if not all("API ERROR" in i or "NOT IN S2" in i for i in iss)]
    api_errors_doi = [(k, iss) for k, iss in doi_issues if all("API ERROR" in i or "NOT IN S2" in i for i in iss)]
    real_search_issues = [(k, iss) for k, iss in search_results if not all("API ERROR" in i for i in iss)]
    api_errors_search = [(k, iss) for k, iss in search_results if all("API ERROR" in i for i in iss)]

    if real_doi_issues:
        print("METADATA ISSUES (entries with DOI):")
        for key, issues in real_doi_issues:
            print(f"\n  {key}:")
            for issue in issues:
                print(f"    {issue}")

    if real_search_issues:
        print("\nFINDINGS (entries without DOI):")
        for key, issues in real_search_issues:
            print(f"\n  {key}:")
            for issue in issues:
                print(f"    {issue}")

    if api_errors_doi or api_errors_search:
        print(f"\nAPI errors prevented checking {len(api_errors_doi) + len(api_errors_search)} entries")

    print(f"\n--- Totals ---")
    print(f"DOI entries verified OK: {doi_ok}/{len(with_doi)}")
    print(f"No-DOI entries verified OK: {search_ok}/{len(without_doi)}")
    print(f"Entries with metadata issues: {len(real_doi_issues)}")
    print(f"Entries with suggested DOIs: {sum(1 for _, iss in real_search_issues if any('SUGGESTED DOI' in i for i in iss))}")
    print(f"Entries blocked by API errors: {len(api_errors_doi) + len(api_errors_search)}")


if __name__ == "__main__":
    main()
