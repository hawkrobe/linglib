#!/usr/bin/env python3
"""Generate typed dependency-length rows from canonical per-paper JSON.

Per-language corpus statistics a paper prints — the proportion of head-final
dependencies and the mean dependency length per word at fixed sentence
lengths, measured over Universal Dependencies treebanks — are canonical JSON
at `Linglib/Data/UD/DependencyLength/<Paper>.json`; this emits the
kernel-reducible typed Lean module
`Linglib/Data/UD/DependencyLength/<Paper>.lean` (`<Paper>.rows`). Mirrors
`gen_protoroles.py`: the generated Lean is never hand-edited — edit the JSON
and re-run.

    python3 scripts/gen_ud_deplength.py FutrellEtAl2020       # (re)generate
    python3 scripts/gen_ud_deplength.py --check [<Paper>]     # verify, no writes (CI)
    python3 scripts/gen_ud_deplength.py --all                 # every JSON
"""
import sys, json, re, textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "UD" / "DependencyLength"
FIELDS = ["propHeadFinal1000", "depLengthAt10_100", "depLengthAt15_100", "depLengthAt20_100"]


def row_lit(r: dict) -> str:
    nums = ", ".join(str(int(r[f])) for f in FIELDS)
    return f"⟨{json.dumps(r['language'])}, {json.dumps(r['isoCode'])}, {nums}⟩"


def render(paper: str, meta: dict, rows: list) -> str:
    lits = ",\n   ".join(row_lit(r) for r in rows)
    return f"""import Linglib.Data.UD.DependencyLength.Schema

/-!
# {paper} — dependency length by language (generated)
[{meta['bibkey']}]

Auto-generated from `Linglib/Data/UD/DependencyLength/{paper}.json` by
`scripts/gen_ud_deplength.py`. **Do not edit by hand** — edit the JSON and
re-run the generator.

{textwrap.fill(meta['description'], 96)}
-/

namespace Data.UD.DependencyLength.{paper}

/-- The {len(rows)} languages of {meta['locator']}, in the paper's row order. -/
def rows : List Row :=
  [{lits}]

end Data.UD.DependencyLength.{paper}
"""


def ensure_import(file_path: Path, module: str) -> bool:
    body = file_path.read_text(encoding="utf-8")
    stmt = f"import {module}"
    if re.search(rf"^{re.escape(stmt)}\s*$", body, flags=re.M):
        return False
    lines = body.splitlines(keepends=True)
    last = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
    lines.insert(last + 1, stmt + "\n")
    file_path.write_text("".join(lines), encoding="utf-8")
    return True


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
        for mod in (f"Linglib.Data.UD.DependencyLength.{paper}",
                    "Linglib.Data.UD.DependencyLength.Schema"):
            if f"import {mod}" not in (ROOT / "Linglib.lean").read_text(encoding="utf-8"):
                sys.stderr.write(f"[check] DRIFT: {mod} missing from Linglib.lean\n")
                return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync ({len(doc['rows'])} rows)\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {json_path.relative_to(ROOT)} ({len(doc['rows'])} rows)\n")
    ensure_import(ROOT / "Linglib.lean", "Linglib.Data.UD.DependencyLength.Schema")
    if ensure_import(ROOT / "Linglib.lean", f"Linglib.Data.UD.DependencyLength.{paper}"):
        sys.stdout.write(f"[gen] added Linglib.Data.UD.DependencyLength.{paper} import to Linglib.lean\n")
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
