#!/usr/bin/env python3
"""Validate `sources` field paths in references.bib against the filesystem.

Each entry's `sources = {path1;path2;...}` lists Lean files (relative to
`Linglib/`) that consume the cited work. This script verifies each path
exists. Stale paths (from renames, deletions) are reported.
"""
import re, os, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent  # scripts/ → blog/ → repo root
BIB = ROOT / "blog" / "data" / "references.bib"
LINGLIB = ROOT / "Linglib"

def parse_entries(text):
    """Yield (key, sources_field) for each @entry."""
    pattern = re.compile(r'^@\w+\{([^,]+),', re.MULTILINE)
    for m in pattern.finditer(text):
        key = m.group(1).strip()
        # Find the matching closing }
        start = m.end()
        depth = 1
        i = start
        while i < len(text) and depth > 0:
            if text[i] == '{': depth += 1
            elif text[i] == '}': depth -= 1
            i += 1
        body = text[start:i-1]
        sm = re.search(r'sources\s*=\s*\{([^}]*)\}', body, re.DOTALL)
        if sm:
            yield key, sm.group(1)

def main():
    text = BIB.read_text()
    stale = []
    total_entries = 0
    total_paths = 0
    for key, srcs in parse_entries(text):
        total_entries += 1
        for p in srcs.split(';'):
            p = p.strip()
            if not p: continue
            total_paths += 1
            full = LINGLIB / p
            if not full.exists():
                stale.append((key, p))
    if stale:
        print(f"Stale source paths: {len(stale)} (across {total_entries} entries with sources, {total_paths} total paths)")
        for key, p in stale:
            print(f"  {key}: {p}")
        sys.exit(1)
    print(f"OK: {total_paths} source paths across {total_entries} entries all exist.")

if __name__ == "__main__":
    main()
