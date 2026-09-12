#!/usr/bin/env python3
"""Generate typed treebank-coverage rows from canonical per-paper JSON.

Per-treebank statistics a paper prints on how many dependency trees, or
grammar rules extracted from them, satisfy a constraint on non-projectivity
are canonical JSON at `Linglib/Data/Treebank/Coverage/<Paper>.json`; this
emits the kernel-reducible typed Lean module
`Linglib/Data/Treebank/Coverage/<Paper>.lean` (`<Paper>.rows`). The
generated Lean is never hand-edited: edit the JSON and re-run.

A JSON row gives the covered quantity either as `value` at the row's `scale`
(`count` or `percentHundredths`) or, for papers that print losses, as `lost`,
a count the generator subtracts from `total`. Constraints are written
`projective`, `gapDegreeEq:k`, `gapDegreeLe:k`, `wellNested`, `planar`, or
`gapDegreeLeWellNested:k`.

    python3 scripts/gen_treebank_coverage.py Kuhlmann2013       # (re)generate
    python3 scripts/gen_treebank_coverage.py --check [<Paper>]  # verify, no writes (CI)
    python3 scripts/gen_treebank_coverage.py --all              # every JSON
"""
import sys, json, textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "Treebank" / "Coverage"
ITEMS = {"trees", "rules"}
SCALES = {"count", "percentHundredths"}
UNARY = {"projective", "wellNested", "planar"}
INDEXED = {"gapDegreeEq", "gapDegreeLe", "gapDegreeLeWellNested"}


def constraint_lit(s: str, where: str) -> str:
    if s in UNARY:
        return f".{s}"
    name, _, k = s.partition(":")
    if name in INDEXED and k.isdigit():
        return f".{name} {int(k)}"
    sys.stderr.write(f"FATAL: {where}: unknown constraint {s!r}\n")
    sys.exit(1)


def row_lit(r: dict, where: str) -> str:
    if r["item"] not in ITEMS:
        sys.stderr.write(f"FATAL: {where}: unknown item {r['item']!r}\n")
        sys.exit(1)
    total = int(r["total"])
    if "lost" in r:
        scale, value = "count", total - int(r["lost"])
    else:
        scale, value = r["scale"], int(r["value"])
    if scale not in SCALES:
        sys.stderr.write(f"FATAL: {where}: unknown scale {scale!r}\n")
        sys.exit(1)
    if scale == "count" and value > total:
        sys.stderr.write(f"FATAL: {where}: covered count exceeds total\n")
        sys.exit(1)
    return (f"⟨{json.dumps(r['treebank'])}, {json.dumps(r['language'])}, .{r['item']}, "
            f"{total}, {constraint_lit(r['constraint'], where)}, .{scale}, {value}⟩")


def render(paper: str, meta: dict, rows: list) -> str:
    lits = ",\n   ".join(row_lit(r, f"{paper}.rows[{i}]") for i, r in enumerate(rows))
    return f"""import Linglib.Data.Treebank.Coverage.Schema

/-!
# {paper} — treebank coverage (generated)
[{meta['bibkey']}]

Auto-generated from `Linglib/Data/Treebank/Coverage/{paper}.json` by
`scripts/gen_treebank_coverage.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

{textwrap.fill(meta['description'], 96)}
-/

namespace Data.Treebank.Coverage.{paper}

/-- The {len(rows)} rows of {meta['locator']}, in the paper's row order. -/
def rows : List Row :=
  [{lits}]

end Data.Treebank.Coverage.{paper}
"""


def process(paper: str, check: bool) -> bool:
    json_path = DATA_DIR / f"{paper}.json"
    if not json_path.exists():
        sys.stderr.write(f"FATAL: JSON not found at {json_path.relative_to(ROOT)}\n")
        sys.exit(1)
    doc = json.loads(json_path.read_text(encoding="utf-8"))
    content = render(paper, doc["meta"], doc["rows"])
    out = DATA_DIR / f"{paper}.lean"
    if check:
        cur = out.read_text(encoding="utf-8") if out.exists() else ""
        if cur != content:
            sys.stderr.write(f"[check] DRIFT: {out.relative_to(ROOT)} out of sync with JSON\n")
            return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync ({len(doc['rows'])} rows)\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {json_path.relative_to(ROOT)} "
                     f"({len(doc['rows'])} rows)\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    if args == ["--all"] or (not args and check):
        papers = sorted(p.stem for p in DATA_DIR.glob("*.json"))
    elif len(args) == 1:
        papers = args
    else:
        sys.stderr.write(__doc__)
        sys.exit(2)
    ok = all(process(p, check) for p in papers)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
