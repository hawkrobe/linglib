#!/usr/bin/env python3
"""Sort the findings of `scripts/verify_bib.py` into what to do about them.

Reads `.lake/build/bibcheck/report.json` and writes `.lake/build/bibcheck/triage.md`:

* entries whose DOI does not resolve, or resolves to another work;
* entries that disagree with a record matched by DOI on a field (year, venue, volume, issue,
  pages, authors, title), with the record's value;
* entries a Crossref search matched but that have no DOI, with the DOI found;
* entries no record matched, the ones linglib cites first;
* entries missing from the Zotero library, the ones linglib cites first, with a DOI where known.
"""

import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / ".lake" / "build" / "bibcheck"
CITE = re.compile(r"\[([a-z0-9][a-z0-9-]*-\d{4}[a-z]?)\]")


def cited_keys():
    files = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True,
                           text=True).stdout.split()
    counts = Counter()
    for f in files:
        try:
            counts.update(set(CITE.findall((ROOT / f).read_text(encoding="utf-8"))))
        except (OSError, UnicodeDecodeError):
            pass
    return counts


def line(r):
    who = r["author"].split(" and ")[0].split(",")[0] if r["author"] else "?"
    return f"`{r['key']}` {who} ({r['year']}), {r['title'][:90]}"


def main():
    report = json.loads((OUT / "report.json").read_text())
    cited = cited_keys()
    by_status = defaultdict(list)
    for r in report:
        by_status[r["status"]].append(r)
    md = ["# Bibliography check", ""]
    md.append(f"{len(report)} entries: " + ", ".join(f"{k} {len(v)}" for k, v in
                                                      sorted(by_status.items())) + ".")
    md.append("")

    # DOIs that do not resolve, or resolve to a different work.
    bad = [r for r in report if r["status"] == "bad-doi"]
    wrong = []
    for r in report:
        for rec in r["records"]:
            if rec["matched"] == "doi" and "title" in rec.get("diffs", {}):
                wrong.append((r, rec))
    md += [f"## DOIs that do not resolve ({len(bad)})", ""]
    md += [f"- {line(r)}: `{r['doi']}`" for r in bad] + [""]
    md += [f"## DOIs whose record has another title ({len(wrong)})", ""]
    for r, rec in wrong:
        md.append(f"- {line(r)}: `{rec['id']}` is *{rec['diffs']['title'][1][:90]}*")
    md.append("")

    # Field disagreements with a DOI-matched record whose title agrees.
    fields = defaultdict(list)
    for r in report:
        for rec in r["records"]:
            d = rec.get("diffs", {})
            if rec["matched"] == "doi" and d and "title" not in d:
                for k, v in d.items():
                    fields[k].append((r, rec["source"], v))
    md += ["## Fields that disagree with the record of the entry's DOI", ""]
    for k in sorted(fields, key=lambda k: -len(fields[k])):
        md += [f"### {k} ({len(fields[k])})", ""]
        md += [f"- {line(r)}: bib `{v[0]}`, {src} `{v[1]}`" for r, src, v in fields[k]] + [""]

    # Search matches: DOIs to add.
    found = [(r, rec) for r in report for rec in r["records"]
             if rec["matched"] == "search" and not rec.get("diffs")]
    md += [f"## DOIs found by search for entries without one ({len(found)})", ""]
    md += [f"- {line(r)}: `{rec['id']}`" for r, rec in found] + [""]

    # Unresolved, cited first.
    un = sorted(by_status["unresolved"], key=lambda r: (-cited.get(r["key"], 0), r["key"]))
    md += [f"## Entries no record matched ({len(un)}; {sum(1 for r in un if cited[r['key']])} "
           "cited in linglib)", ""]
    md += [f"- {line(r)} [{r['type']}]" + (f", cited in {cited[r['key']]} files"
                                           if cited[r["key"]] else "") for r in un] + [""]

    # Missing from Zotero, cited first.
    missing = sorted((r for r in report if not any(rec["source"] == "zotero"
                                                   for rec in r["records"])),
                     key=lambda r: (-cited.get(r["key"], 0), r["key"]))
    md += [f"## Not in the Zotero library ({len(missing)}; "
           f"{sum(1 for r in missing if cited[r['key']])} cited in linglib)", ""]
    for r in missing:
        doi = r["doi"] or next((rec["id"] for rec in r["records"]
                                if rec["source"] == "crossref" and rec["matched"] == "search"), "")
        md.append(f"- {line(r)} [{r['type']}]" + (f", doi `{doi}`" if doi else "")
                  + (f", cited in {cited[r['key']]} files" if cited[r["key"]] else ""))
    (OUT / "triage.md").write_text("\n".join(md) + "\n")
    print(f"wrote {OUT / 'triage.md'}", file=sys.stderr)


if __name__ == "__main__":
    main()
