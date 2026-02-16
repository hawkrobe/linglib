#!/usr/bin/env python3
"""Verify references.bib entries against the Semantic Scholar API.

For entries WITH a DOI: looks up by DOI and verifies metadata.
For entries WITHOUT a DOI: searches by title to find a DOI.

Rate-limited to ~1 request/second to avoid 429 errors.

Usage:
    python blog/scripts/verify_bib.py
"""

import re, json, time, urllib.request, urllib.error, urllib.parse, sys
from pathlib import Path

BIB_PATH = Path(__file__).resolve().parent.parent / "data" / "references.bib"

def parse_bib(path):
    text = path.read_text(encoding="utf-8")
    entries = []
    for m in re.finditer(r'@(\w+)\s*\{([^,]+),\s*(.*?)\n\}', text, re.DOTALL):
        key = m.group(2).strip()
        body = m.group(3)
        fields = {'_key': key, '_type': m.group(1).lower()}
        for fm in re.finditer(r'(\w[\w-]*)\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}', body):
            fields[fm.group(1).lower()] = fm.group(2)
        entries.append(fields)
    return entries

def clean_title(t):
    t = re.sub(r'\{([^{}]*)\}', r'\1', t)
    t = t.replace('\\', '').replace('"', '').replace("'", '')
    return t.strip()

def api_get(url, retries=2):
    """GET with retries and backoff."""
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'linglib-bib-checker/1.0'})
            with urllib.request.urlopen(req, timeout=15) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < retries:
                wait = 5 * (attempt + 1)
                print(f"    Rate limited, waiting {wait}s...", flush=True)
                time.sleep(wait)
            elif e.code == 404:
                return {'error': f'HTTP 404'}
            else:
                return {'error': f'HTTP {e.code}'}
        except Exception as e:
            if attempt < retries:
                time.sleep(2)
            else:
                return {'error': str(e)[:80]}
    return {'error': 'max retries'}

def lookup_by_doi(doi):
    url = f"https://api.semanticscholar.org/graph/v1/paper/DOI:{urllib.parse.quote(doi, safe='')}?fields=title,authors,year,venue,externalIds"
    return api_get(url)

def search_by_title(title):
    q = clean_title(title)[:200]
    params = urllib.parse.urlencode({'query': q, 'limit': '3', 'fields': 'title,authors,year,venue,externalIds'})
    url = f"https://api.semanticscholar.org/graph/v1/paper/search?{params}"
    return api_get(url)

def title_match(bib_title, s2_title):
    bt = clean_title(bib_title).lower()[:50]
    st = (s2_title or '').lower()[:50]
    return bt[:30] in st or st[:30] in bt

def main():
    entries = parse_bib(BIB_PATH)
    print(f"Loaded {len(entries)} entries from {BIB_PATH}\n")

    doi_verified = []
    doi_errors = []
    doi_mismatches = []
    found_dois = []
    no_doi_found = []
    not_found = []
    search_errors = []

    for i, e in enumerate(entries):
        key = e['_key']
        title = e.get('title', '')
        doi = e.get('doi', '')
        year = e.get('year', '')

        # Rate limit: 1 req/sec
        if i > 0:
            time.sleep(1.1)

        if doi:
            result = lookup_by_doi(doi)
            if 'error' in result:
                print(f"[{i+1:3d}] {key:45s} DOI_ERROR  {doi} -> {result['error']}", flush=True)
                doi_errors.append((key, doi, result['error']))
            else:
                s2_title = result.get('title', '')
                s2_year = result.get('year', '')
                issues = []
                if s2_year and str(s2_year) != str(year):
                    issues.append(f"year: bib={year} vs S2={s2_year}")
                if not title_match(title, s2_title):
                    issues.append(f"title: S2='{s2_title[:60]}'")
                if issues:
                    print(f"[{i+1:3d}] {key:45s} MISMATCH   {'; '.join(issues)}", flush=True)
                    doi_mismatches.append((key, doi, issues))
                else:
                    print(f"[{i+1:3d}] {key:45s} DOI_OK", flush=True)
                    doi_verified.append(key)
        else:
            data = search_by_title(title)
            if 'error' in data:
                print(f"[{i+1:3d}] {key:45s} SEARCH_ERR {data['error']}", flush=True)
                search_errors.append((key, data['error']))
                continue

            papers = data.get('data', [])
            if not papers:
                print(f"[{i+1:3d}] {key:45s} NOT_FOUND", flush=True)
                not_found.append(key)
                continue

            # Find best match
            best = None
            for p in papers:
                if title_match(title, p.get('title', '')):
                    best = p
                    break
            if not best:
                best = papers[0]

            s2_doi = (best.get('externalIds') or {}).get('DOI', '')
            s2_title = best.get('title', '') or ''
            s2_year = best.get('year', '')
            matched = title_match(title, s2_title)

            issues = []
            if s2_year and str(s2_year) != str(year):
                issues.append(f"year: bib={year} vs S2={s2_year}")
            if not matched:
                issues.append(f"title mismatch: S2='{s2_title[:50]}'")

            if s2_doi and matched:
                tag = "FOUND_DOI"
                found_dois.append((key, s2_doi, s2_title[:70], issues))
            elif s2_doi and not matched:
                tag = "FOUND_DOI?"
                found_dois.append((key, s2_doi, s2_title[:70], issues))
            else:
                tag = "NO_DOI"
                no_doi_found.append((key, s2_title[:70], issues))

            extra = f" doi={s2_doi}" if s2_doi else ""
            issue_str = f" [{'; '.join(issues)}]" if issues else ""
            print(f"[{i+1:3d}] {key:45s} {tag:10s}{extra}{issue_str}", flush=True)

    # Summary
    print("\n" + "=" * 80)
    print("VERIFICATION SUMMARY")
    print("=" * 80)
    print(f"  DOI verified OK:      {len(doi_verified)}")
    print(f"  DOI errors (bad DOI): {len(doi_errors)}")
    print(f"  DOI mismatches:       {len(doi_mismatches)}")
    print(f"  Found new DOIs:       {len(found_dois)}")
    print(f"  No DOI available:     {len(no_doi_found)}")
    print(f"  Not found on S2:      {len(not_found)}")
    print(f"  Search errors:        {len(search_errors)}")

    if doi_errors:
        print(f"\n--- DOI ERRORS (need fixing) ---")
        for key, doi, err in doi_errors:
            print(f"  {key}: doi={doi} -> {err}")

    if doi_mismatches:
        print(f"\n--- DOI MISMATCHES (check manually) ---")
        for key, doi, issues in doi_mismatches:
            print(f"  {key}: {'; '.join(issues)}")

    if found_dois:
        print(f"\n--- NEW DOIs FOUND (add to .bib) ---")
        for key, doi, s2t, issues in found_dois:
            match_note = " [CHECK TITLE]" if issues else ""
            print(f"  {key}: doi = {{{doi}}}{match_note}")

    if no_doi_found:
        print(f"\n--- NO DOI AVAILABLE (may need URL) ---")
        for key, s2t, issues in no_doi_found:
            issue_str = f" [{'; '.join(issues)}]" if issues else ""
            print(f"  {key}: matched='{s2t}'{issue_str}")

    if not_found:
        print(f"\n--- NOT FOUND ON SEMANTIC SCHOLAR ---")
        for key in not_found:
            print(f"  {key}")

    if search_errors:
        print(f"\n--- SEARCH ERRORS ---")
        for key, err in search_errors:
            print(f"  {key}: {err}")

if __name__ == "__main__":
    main()
