#!/usr/bin/env python3
"""Generate typed `ProtoRoleDatum` literals from canonical proto-role JSON.

The per-argument entailment attributions a paper states explicitly are
canonical JSON at `Linglib/Data/ProtoRoles/<Paper>.json`; this emits the
kernel-reducible typed Lean module `Linglib/Data/ProtoRoles/<Paper>.lean`
(literals in `namespace <Paper>.Rows`, plus `<Paper>.allRows`). Mirrors
`gen_wals.py` / `gen_scalardiversity.py`: the generated Lean is never
hand-edited — edit the JSON and re-run.

    python3 scripts/gen_protoroles.py Dowty1991          # (re)generate
    python3 scripts/gen_protoroles.py --check [<Paper>]  # verify, no writes (CI)
    python3 scripts/gen_protoroles.py --all              # every JSON
"""
import sys, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "ProtoRoles"

ENTAILMENTS = [
    "volition", "sentience", "causation", "movement", "independentExistence",
    "changeOfState", "incrementalTheme", "causallyAffected", "stationary",
    "dependentExistence",
]


def opt_bool(v) -> str:
    return "none" if v is None else f"some {str(v).lower()}"


def datum_def(r: dict) -> str:
    stated = [e for e in ENTAILMENTS if r.get(e) is not None]
    fields = ",\n    ".join(f"{e} := {opt_bool(r[e])}" for e in stated)
    body = f"  {{ verb := {json.dumps(r['verb'])}, arg := .{r['arg']},\n"
    body += f"    argDesc := {json.dumps(r['argDesc'])},\n"
    if fields:
        body += f"    {fields},\n"
    body += f"    locator := {json.dumps(r['locator'])} }}"
    return f"def {r['name']} : ProtoRoleDatum :=\n{body}"


def render(paper: str, rows: list) -> str:
    defs = "\n\n".join(datum_def(r) for r in rows)
    names = ",\n   ".join(f"Rows.{r['name']}" for r in rows)
    return f"""import Linglib.Data.ProtoRoles.Schema

/-!
# {paper} — proto-role attribution data (generated)
[dowty-1991]

Auto-generated from `Linglib/Data/ProtoRoles/{paper}.json` by
`scripts/gen_protoroles.py`. **Do not edit by hand** — edit the JSON and
re-run the generator. The {len(rows)} per-argument entailment attributions
the paper states explicitly, with locators; fields the paper is silent or
hedged about are `none`.
-/

namespace {paper}

namespace Rows

{defs}

end Rows

/-- All {len(rows)} explicit per-argument attributions. -/
def allRows : List ProtoRoleDatum :=
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
        for mod in (f"Linglib.Data.ProtoRoles.{paper}",
                    "Linglib.Data.ProtoRoles.Schema"):
            if f"import {mod}" not in (ROOT / "Linglib.lean").read_text(encoding="utf-8"):
                sys.stderr.write(f"[check] DRIFT: {mod} missing from Linglib.lean\n")
                return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync ({len(rows)} rows)\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {json_path.relative_to(ROOT)} ({len(rows)} rows)\n")
    ensure_import(ROOT / "Linglib.lean", "Linglib.Data.ProtoRoles.Schema")
    if ensure_import(ROOT / "Linglib.lean", f"Linglib.Data.ProtoRoles.{paper}"):
        sys.stdout.write(f"[gen] added Linglib.Data.ProtoRoles.{paper} import to Linglib.lean\n")
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
