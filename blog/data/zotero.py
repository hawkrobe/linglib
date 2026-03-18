#!/usr/bin/env python3
"""
Batch-import bibliography entries into Zotero from a .bib file.

Strategy:
  1. Entries WITH DOIs → look up via Zotero's translation server (metadata + type)
  2. Entries WITHOUT DOIs → import directly from BibTeX fields
  3. After import → trigger "Find Available PDF" for each item

Usage:
  1. Get your Zotero API key from https://www.zotero.org/settings/keys/new
     - Check "Allow library access"
     - Check "Allow write access"
  2. Get your library ID from https://www.zotero.org/settings/keys
     (it's your userID, shown at the top of the page)
  3. Run:
     python3 zotero_import.py --api-key YOUR_KEY --library-id YOUR_ID

Options:
  --collection NAME    Create/use a collection for these items (default: "linglib")
  --dry-run            Parse and report without actually importing
  --batch-size N       Items per API call (default: 50, max 50)
  --start-from N       Skip first N entries (for resuming interrupted imports)
  --limit N            Only import first N entries (for testing)
"""

import argparse
import json
import time
import sys
import re
import urllib.request
import urllib.error
from pathlib import Path

try:
    from pyzotero import zotero
except ImportError:
    print("Install pyzotero: pip install pyzotero")
    sys.exit(1)

try:
    import bibtexparser
except ImportError:
    print("Install bibtexparser: pip install bibtexparser")
    sys.exit(1)


# ── BibTeX → Zotero type mapping ──────────────────────────────────────────

BIBTEX_TO_ZOTERO_TYPE = {
    "article": "journalArticle",
    "inproceedings": "conferencePaper",
    "incollection": "bookSection",
    "book": "book",
    "phdthesis": "thesis",
    "mastersthesis": "thesis",
    "techreport": "report",
    "misc": "document",
    "unpublished": "manuscript",
    "inbook": "bookSection",
    "proceedings": "book",
    "manual": "document",
}


def clean_bibtex_str(s):
    """Remove BibTeX braces and common LaTeX commands."""
    if not s:
        return ""
    s = s.replace("{", "").replace("}", "")
    s = s.replace("\\&", "&")
    s = s.replace("\\_", "_")
    s = s.replace("\\textendash", "–")
    s = s.replace("--", "–")
    # Handle \"u → ü etc.
    accent_map = {
        '\\"a': 'ä', '\\"o': 'ö', '\\"u': 'ü', '\\"e': 'ë', '\\"i': 'ï',
        '\\"A': 'Ä', '\\"O': 'Ö', '\\"U': 'Ü',
        "\\'a": 'á', "\\'e": 'é', "\\'i": 'í', "\\'o": 'ó', "\\'u": 'ú',
        "\\'A": 'Á', "\\'E": 'É', "\\'I": 'Í', "\\'O": 'Ó', "\\'U": 'Ú',
        "\\`a": 'à', "\\`e": 'è', "\\`i": 'ì', "\\`o": 'ò', "\\`u": 'ù',
        "\\^a": 'â', "\\^e": 'ê', "\\^i": 'î', "\\^o": 'ô', "\\^u": 'û',
        "\\~n": 'ñ', "\\~a": 'ã', "\\~o": 'õ',
        "\\c{c}": 'ç', "\\cc": 'ç',
        "\\ss": 'ß',
    }
    for latex, uni in accent_map.items():
        s = s.replace(latex, uni)
    return s.strip()


def parse_authors(author_str):
    """Parse BibTeX author string into Zotero creator dicts."""
    if not author_str:
        return []
    creators = []
    # Split on " and "
    authors = re.split(r'\s+and\s+', author_str)
    for a in authors:
        a = clean_bibtex_str(a).strip()
        if not a:
            continue
        if ',' in a:
            parts = a.split(',', 1)
            creators.append({
                "creatorType": "author",
                "lastName": parts[0].strip(),
                "firstName": parts[1].strip(),
            })
        else:
            parts = a.rsplit(' ', 1)
            if len(parts) == 2:
                creators.append({
                    "creatorType": "author",
                    "lastName": parts[1].strip(),
                    "firstName": parts[0].strip(),
                })
            else:
                creators.append({
                    "creatorType": "author",
                    "lastName": a,
                    "firstName": "",
                })
    return creators


def bib_entry_to_zotero_item(entry, template_cache, zot):
    """Convert a bibtexparser entry dict to a Zotero API item dict."""
    entry_type = entry.get("ENTRYTYPE", "misc").lower()
    zotero_type = BIBTEX_TO_ZOTERO_TYPE.get(entry_type, "document")

    # Get or cache the template
    if zotero_type not in template_cache:
        template_cache[zotero_type] = zot.item_template(zotero_type)
    item = dict(template_cache[zotero_type])  # shallow copy

    item["title"] = clean_bibtex_str(entry.get("title", ""))
    item["creators"] = parse_authors(entry.get("author", ""))
    item["date"] = entry.get("year", "")
    item["DOI"] = entry.get("doi", "").strip()
    item["abstractNote"] = clean_bibtex_str(entry.get("abstract", ""))
    item["url"] = entry.get("url", "").strip()
    item["ISBN"] = entry.get("isbn", "")

    if zotero_type == "journalArticle":
        item["publicationTitle"] = clean_bibtex_str(entry.get("journal", ""))
        item["volume"] = entry.get("volume", "")
        item["issue"] = entry.get("number", "")
        item["pages"] = entry.get("pages", "").replace("--", "–")
    elif zotero_type == "conferencePaper":
        item["proceedingsTitle"] = clean_bibtex_str(entry.get("booktitle", ""))
        item["pages"] = entry.get("pages", "").replace("--", "–")
    elif zotero_type == "bookSection":
        item["bookTitle"] = clean_bibtex_str(entry.get("booktitle", ""))
        item["pages"] = entry.get("pages", "").replace("--", "–")
        # Add editors if present
        if entry.get("editor"):
            for ed in parse_authors(entry.get("editor", "")):
                ed["creatorType"] = "editor"
                item["creators"].append(ed)
    elif zotero_type == "book":
        item["publisher"] = clean_bibtex_str(entry.get("publisher", ""))
        if entry.get("edition"):
            item["edition"] = entry.get("edition", "")
    elif zotero_type == "thesis":
        item["university"] = clean_bibtex_str(entry.get("school", ""))
        if entry_type == "phdthesis":
            item["thesisType"] = "PhD Thesis"
        elif entry_type == "mastersthesis":
            item["thesisType"] = "Master's Thesis"
    elif zotero_type == "report":
        item["institution"] = clean_bibtex_str(entry.get("institution", ""))

    # Add BibTeX key as an extra field for traceability
    item["extra"] = f"bibtex: {entry.get('ID', '')}"

    return item


def lookup_doi_via_translation(doi):
    """
    Use Zotero's public translation server to get item metadata from a DOI.
    Returns a Zotero item dict, or None on failure.
    """
    url = "https://translate.manubot.org/web"
    data = json.dumps(doi if doi.startswith("http") else f"https://doi.org/{doi}").encode()
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("Content-Type", "text/plain")
    try:
        resp = urllib.request.urlopen(req, timeout=15)
        items = json.loads(resp.read())
        if items and len(items) > 0:
            return items[0]
    except Exception:
        pass
    return None


def get_or_create_collection(zot, name):
    """Find or create a top-level collection by name. Returns collection key."""
    collections = zot.collections()
    for c in collections:
        if c["data"]["name"].lower() == name.lower():
            print(f"  Found existing collection: {name} ({c['key']})")
            return c["key"]
    # Create it
    resp = zot.create_collection([{"name": name}])
    if "successful" in resp and resp["successful"]:
        key = list(resp["successful"].values())[0]["data"]["key"]
        print(f"  Created collection: {name} ({key})")
        return key
    # Fallback: try to parse response
    if "success" in resp and resp["success"]:
        key = list(resp["success"].values())[0]
        print(f"  Created collection: {name} ({key})")
        return key
    print(f"  Warning: could not create collection '{name}': {resp}")
    return None


def main():
    parser = argparse.ArgumentParser(description="Import linglib bibliography into Zotero")
    parser.add_argument("--api-key", required=True, help="Zotero API key")
    parser.add_argument("--library-id", required=True, help="Zotero user/library ID")
    parser.add_argument("--library-type", default="user", choices=["user", "group"])
    parser.add_argument("--collection", default="linglib", help="Collection name")
    parser.add_argument("--bib-file", default="./references.bib")
    parser.add_argument("--dry-run", action="store_true", help="Parse only, don't import")
    parser.add_argument("--batch-size", type=int, default=50)
    parser.add_argument("--start-from", type=int, default=0, help="Skip first N entries")
    parser.add_argument("--limit", type=int, default=0, help="Import at most N entries (0=all)")
    parser.add_argument("--use-translation", action="store_true",
                        help="Use Zotero translation server for DOI lookup (slower but richer metadata)")
    parser.add_argument("--skip-doi-entries", action="store_true",
                        help="Only import entries WITHOUT DOIs (use if DOI entries already imported)")
    parser.add_argument("--skip-no-doi-entries", action="store_true",
                        help="Only import entries WITH DOIs")
    args = parser.parse_args()

    # ── Parse BibTeX ──
    print("Parsing BibTeX file...")
    with open(args.bib_file) as f:
        db = bibtexparser.load(f)

    TARGET_ROLES = {"cited", "formalized", "foundational"}
    entries = [e for e in db.entries if e.get("role", "").strip() in TARGET_ROLES]
    print(f"  {len(entries)} entries with matching roles")

    if args.skip_doi_entries:
        entries = [e for e in entries if not e.get("doi", "").strip()]
        print(f"  Filtered to {len(entries)} entries WITHOUT DOIs")
    elif args.skip_no_doi_entries:
        entries = [e for e in entries if e.get("doi", "").strip()]
        print(f"  Filtered to {len(entries)} entries WITH DOIs")

    # Apply start-from and limit
    if args.start_from > 0:
        entries = entries[args.start_from:]
        print(f"  Starting from entry {args.start_from}, {len(entries)} remaining")
    if args.limit > 0:
        entries = entries[:args.limit]
        print(f"  Limited to {len(entries)} entries")

    if args.dry_run:
        print(f"\n[DRY RUN] Would import {len(entries)} entries.")
        has_doi = sum(1 for e in entries if e.get("doi", "").strip())
        print(f"  {has_doi} with DOIs, {len(entries) - has_doi} without")
        return

    # ── Connect to Zotero ──
    print(f"\nConnecting to Zotero ({args.library_type} library {args.library_id})...")
    zot = zotero.Zotero(args.library_id, args.library_type, args.api_key)

    # Verify connection
    try:
        zot.key_info()
        print("  Connected successfully!")
    except Exception as e:
        print(f"  ERROR: Could not connect to Zotero: {e}")
        sys.exit(1)

    # Get/create collection
    collection_key = None
    if args.collection:
        print(f"Setting up collection '{args.collection}'...")
        collection_key = get_or_create_collection(zot, args.collection)

    # ── Import entries ──
    template_cache = {}
    items_to_create = []
    failed = []
    succeeded = 0
    doi_lookup_count = 0

    print(f"\nPreparing {len(entries)} items for import...")
    for i, entry in enumerate(entries):
        doi = entry.get("doi", "").strip()
        item = None

        # Try DOI lookup via translation server if requested
        if doi and args.use_translation:
            doi_lookup_count += 1
            item_data = lookup_doi_via_translation(doi)
            if item_data:
                # Translation server returns Zotero-compatible items
                item = item_data
                # Ensure it's in the right format for the API
                if "key" in item:
                    del item["key"]
                if "version" in item:
                    del item["version"]
            if doi_lookup_count % 10 == 0:
                time.sleep(1)  # Rate limit

        # Fallback: build from BibTeX fields
        if item is None:
            item = bib_entry_to_zotero_item(entry, template_cache, zot)

        # Assign to collection
        if collection_key:
            item["collections"] = [collection_key]

        # Tag with linglib role
        role = entry.get("role", "").strip()
        subfield = entry.get("subfield", "").strip()
        item["tags"] = item.get("tags", [])
        if role:
            item["tags"].append({"tag": f"linglib:{role}"})
        if subfield:
            item["tags"].append({"tag": f"linglib:{subfield}"})

        items_to_create.append(item)

        if (i + 1) % 100 == 0:
            print(f"  Prepared {i+1}/{len(entries)}...")

    # ── Batch upload ──
    print(f"\nUploading {len(items_to_create)} items in batches of {args.batch_size}...")
    all_created_keys = []

    for batch_start in range(0, len(items_to_create), args.batch_size):
        batch = items_to_create[batch_start:batch_start + args.batch_size]
        batch_num = batch_start // args.batch_size + 1
        total_batches = (len(items_to_create) + args.batch_size - 1) // args.batch_size

        try:
            resp = zot.create_items(batch)

            if "successful" in resp:
                n_success = len(resp["successful"])
                succeeded += n_success
                for idx_str, item_data in resp["successful"].items():
                    if isinstance(item_data, dict):
                        all_created_keys.append(item_data.get("key") or
                                                item_data.get("data", {}).get("key", ""))

            if "failed" in resp and resp["failed"]:
                for idx_str, err in resp["failed"].items():
                    idx = int(idx_str)
                    actual_idx = batch_start + idx
                    entry = entries[actual_idx] if actual_idx < len(entries) else {}
                    failed.append({
                        "key": entry.get("ID", "?"),
                        "error": str(err),
                    })

            print(f"  Batch {batch_num}/{total_batches}: "
                  f"{len(resp.get('successful', {}))} ok, "
                  f"{len(resp.get('failed', {}))} failed")

        except Exception as e:
            print(f"  Batch {batch_num}/{total_batches}: ERROR - {e}")
            for j in range(len(batch)):
                actual_idx = batch_start + j
                entry = entries[actual_idx] if actual_idx < len(entries) else {}
                failed.append({"key": entry.get("ID", "?"), "error": str(e)})

        # Rate limit between batches
        time.sleep(0.5)

    # ── Summary ──
    print(f"\n{'='*60}")
    print(f"IMPORT COMPLETE")
    print(f"{'='*60}")
    print(f"  Succeeded: {succeeded}")
    print(f"  Failed:    {len(failed)}")
    print(f"  Total:     {len(entries)}")

    if failed:
        print(f"\nFailed entries:")
        for f_entry in failed[:20]:
            print(f"  {f_entry['key']}: {f_entry['error'][:80]}")
        if len(failed) > 20:
            print(f"  ... and {len(failed) - 20} more")

    # Save results
    results = {
        "succeeded": succeeded,
        "failed_count": len(failed),
        "failed": failed,
        "created_keys": all_created_keys,
    }
    results_path = Path("import_results.json")
    with open(results_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nDetailed results saved to {results_path}")

    # ── PDF retrieval note ──
    print(f"""
{'='*60}
NEXT STEP: Fetch PDFs
{'='*60}
The items are now in your Zotero library. To attach PDFs:

Option A (easiest): In the Zotero desktop app:
  1. Select all items in the 'linglib' collection (Ctrl/Cmd+A)
  2. Right-click → "Find Available PDF"
  Zotero will attempt to download PDFs from publisher sites,
  open-access repositories, and your configured proxy.

Option B: Install the zotero-scihub plugin:
  https://github.com/ethanwillis/zotero-scihub
  Then right-click items → "Find PDF from Sci-Hub"

Option C: Use Zotero's auto-retrieval:
  Edit → Preferences → General → "Automatically attach associated PDFs"
  (works when adding items, so mainly useful going forward)
""")


if __name__ == "__main__":
    main()
