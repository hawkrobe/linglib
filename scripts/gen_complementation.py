#!/usr/bin/env python3
"""Generate typed `Datum` literals from canonical complementation JSON.

The complement-taking-predicate sample of a complementation study is canonical
JSON at `Linglib/Data/Complementation/<Paper>.json` (an object mapping language
keys to row arrays); this emits the kernel-reducible typed Lean module
`Linglib/Data/Complementation/<Paper>.lean` (per-row defs, per-language lists,
`sample`, `all` in `namespace Data.Complementation.<Paper>`). Mirrors
`gen_wals.py`: the generated Lean is never hand-edited — edit the JSON and
re-run. The `Linglib.lean` root import is kept in sync automatically.

    python3 scripts/gen_complementation.py Noonan2007         # (re)generate
    python3 scripts/gen_complementation.py --check [<Paper>]  # verify, no writes (CI)
    python3 scripts/gen_complementation.py --all              # every JSON
"""
import sys, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "Complementation"

BIB_KEY = {"Noonan2007": "noonan-2007"}


def datum_def(r: dict) -> str:
    comps = ", ".join(f".{c}" for c in r["compTypes"])
    verb = json.dumps(r["verb"], ensure_ascii=False)
    flags = f"{str(r['hasEquiDeletion']).lower()}, {str(r['hasNegativeRaising']).lower()}"
    return (
        f"def {r['name']} : Datum :=\n"
        f"  ⟨{verb}, .{r['ctpClass']}, [{comps}], {flags}⟩"
    )


def name_list(names: list, indent: str = "  ") -> str:
    """Render `[a, b, …]` wrapped at ~96 columns."""
    lines, cur = [], indent + "["
    for i, n in enumerate(names):
        item = n + ("]" if i == len(names) - 1 else ",")
        if len(cur) + len(item) + 1 > 96 and cur.strip() != "[":
            lines.append(cur.rstrip())
            cur = indent + " " + item
        else:
            cur += (" " if cur.strip() != "[" and not cur.endswith("[") else "") + item
    lines.append(cur)
    return "\n".join(lines)


def render(paper: str, data: dict) -> str:
    key = BIB_KEY.get(paper, paper)
    langs = list(data.keys())
    total = sum(len(rows) for rows in data.values())
    blocks = []
    for lang in langs:
        rows = data[lang]
        defs = "\n\n".join(datum_def(r) for r in rows)
        lst = name_list([r["name"] for r in rows])
        blocks.append(
            f"{defs}\n\n"
            f"/-- The `{lang}` rows of the sample ({len(rows)} rows). -/\n"
            f"def {lang} : List Datum :=\n{lst}"
        )
    body = "\n\n".join(blocks)
    sample = name_list(langs)
    return f"""import Linglib.Data.Complementation.Schema

/-!
# {paper} — complement-taking-predicate sample (generated)
[{key}]

Auto-generated from `Linglib/Data/Complementation/{paper}.json` by
`scripts/gen_complementation.py`. **Do not edit by hand** — edit the JSON and
re-run the generator. The {total} CTP rows of [{key}]'s {len(langs)}-language
sample: per-row CTP class, attested complement types, equi-deletion, and
negative raising.
-/

namespace Data.Complementation.{paper}

{body}

/-- The {len(langs)}-language sample, one row list per language. -/
def sample : List (List Datum) :=
{sample}

/-- All {total} rows of the sample, pooled. -/
def all : List Datum := sample.flatten

end Data.Complementation.{paper}
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
    data = json.loads(json_path.read_text(encoding="utf-8"))
    content = render(paper, data)
    out = DATA_DIR / f"{paper}.lean"
    total = sum(len(rows) for rows in data.values())
    if check:
        cur = out.read_text(encoding="utf-8") if out.exists() else ""
        if cur != content:
            sys.stderr.write(f"[check] DRIFT: {out.relative_to(ROOT)} out of sync with JSON\n")
            return False
        root = (ROOT / "Linglib.lean").read_text(encoding="utf-8")
        for mod in (f"Linglib.Data.Complementation.{paper}",
                    "Linglib.Data.Complementation.Schema"):
            if f"import {mod}" not in root:
                sys.stderr.write(f"[check] DRIFT: {mod} missing from Linglib.lean\n")
                return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync ({total} rows)\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {json_path.relative_to(ROOT)} ({total} rows)\n")
    ensure_import(ROOT / "Linglib.lean", "Linglib.Data.Complementation.Schema")
    if ensure_import(ROOT / "Linglib.lean", f"Linglib.Data.Complementation.{paper}"):
        sys.stdout.write(f"[gen] added Linglib.Data.Complementation.{paper} import to Linglib.lean\n")
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
