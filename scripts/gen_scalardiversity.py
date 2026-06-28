#!/usr/bin/env python3
"""Generate typed `ScaleDatum` literals from canonical scalar-diversity JSON.

The per-scale data matrix of a scalar-diversity study is canonical JSON at
`Linglib/Data/ScalarDiversity/<Paper>.json`; this emits the kernel-reducible
typed Lean module `Linglib/Data/ScalarDiversity/<Paper>.lean` (literals in
`namespace <Paper>.Scales`, plus `<Paper>.allScales`). Mirrors `gen_wals.py`:
the generated Lean is never hand-edited — edit the JSON and re-run.

    python3 scripts/gen_scalardiversity.py VanTielEtAl2016     # (re)generate
    python3 scripts/gen_scalardiversity.py --check [<Paper>]   # verify, no writes (CI)
    python3 scripts/gen_scalardiversity.py --all               # every JSON
"""
import sys, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "ScalarDiversity"


def q_lit(x: float) -> str:
    """A float to a `ℚ` literal `N/100` (the columns are two-decimal)."""
    return f"{round(x * 100)}/100"


def opt_nat(v) -> str:
    return f"some {v}" if v is not None else "none"


def opt_q(v) -> str:
    return f"some ({q_lit(v)})" if v is not None else "none"


def datum_def(r: dict) -> str:
    return (
        f"def {r['name']} : ScaleDatum :=\n"
        f"  {{ weakerTerm := {json.dumps(r['weaker'])}, "
        f"strongerTerm := {json.dumps(r['stronger'])}, category := .{r['category']},\n"
        f"    siRateExp1 := {r['siExp1']}, siRateExp2 := {r['siExp2']},\n"
        f"    clozeNeutral := {opt_nat(r['clozeNeutral'])}, "
        f"clozeNonNeutral := {opt_nat(r['clozeNonNeutral'])},\n"
        f"    freqRatio := {opt_q(r['freqRatio'])}, "
        f"lsaRelatedness := {opt_q(r['lsa'])},\n"
        f"    semanticDistance := {q_lit(r['semanticDistance'])}, "
        f"bounded := {str(r['bounded']).lower()} }}"
    )


def render(paper: str, rows: list) -> str:
    defs = "\n\n".join(datum_def(r) for r in rows)
    names = ", ".join(f"Scales.{r['name']}" for r in rows)
    return f"""import Linglib.Data.ScalarDiversity.Schema

/-!
# {paper} — scalar-diversity data (generated)
[van-tiel-geurts-2016]

Auto-generated from `Linglib/Data/ScalarDiversity/{paper}.json` by
`scripts/gen_scalardiversity.py`. **Do not edit by hand** — edit the JSON and
re-run the generator. The {len(rows)} lexical scales of [van-tiel-geurts-2016]
(Table 3): SI rates, cloze rates, frequency ratio, LSA relatedness, semantic
distance, and boundedness.
-/

namespace {paper}

namespace Scales

{defs}

end Scales

/-- All {len(rows)} lexical scales ([van-tiel-geurts-2016], Table 3). -/
def allScales : List ScaleDatum :=
  [{names}]

end {paper}
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
    rows = json.loads(json_path.read_text(encoding="utf-8"))
    content = render(paper, rows)
    out = DATA_DIR / f"{paper}.lean"
    if check:
        cur = out.read_text(encoding="utf-8") if out.exists() else ""
        if cur != content:
            sys.stderr.write(f"[check] DRIFT: {out.relative_to(ROOT)} out of sync with JSON\n")
            return False
        for mod in (f"Linglib.Data.ScalarDiversity.{paper}",
                    "Linglib.Data.ScalarDiversity.Schema"):
            if f"import {mod}" not in (ROOT / "Linglib.lean").read_text(encoding="utf-8"):
                sys.stderr.write(f"[check] DRIFT: {mod} missing from Linglib.lean\n")
                return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync ({len(rows)} scales)\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {json_path.relative_to(ROOT)} ({len(rows)} scales)\n")
    ensure_import(ROOT / "Linglib.lean", "Linglib.Data.ScalarDiversity.Schema")
    if ensure_import(ROOT / "Linglib.lean", f"Linglib.Data.ScalarDiversity.{paper}"):
        sys.stdout.write(f"[gen] added Linglib.Data.ScalarDiversity.{paper} import to Linglib.lean\n")
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
