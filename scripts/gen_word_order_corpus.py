#!/usr/bin/env python3
"""Generate typed corpus word-order rows from canonical per-paper JSON.

The word-order data a paper draws from corpora — per-language counts of the two orders of
subject and object, per-language printed order statistics, and individually annotated
clauses — is canonical JSON at `Linglib/Data/WordOrder/Corpus/<Paper>.json`; this emits the
kernel-reducible typed Lean module `Linglib/Data/WordOrder/Corpus/<Paper>.lean`, one `List`
per table present in the JSON. Mirrors `gen_ud_deplength.py`: the generated Lean is never
hand-edited — edit the JSON and re-run. `Linglib.lean` is not touched; `scripts/mk_all.py`
regenerates it before a release.

    python3 scripts/gen_word_order_corpus.py LevshinaEtAl2023    # (re)generate
    python3 scripts/gen_word_order_corpus.py --check [<Paper>]   # verify, no writes (CI)
    python3 scripts/gen_word_order_corpus.py --all               # every JSON
"""
import sys, json, textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "WordOrder" / "Corpus"

# JSON key → (Lean type, fields as (name, kind)); kinds: str, nat, enum, bool.
TABLES = {
    "subjectObjectCounts": ("SubjectObjectCounts", [
        ("language", "str"), ("isoCode", "str"), ("subjectFirst", "nat"), ("objectFirst", "nat")]),
    "subjectObjectStatistics": ("SubjectObjectStatistics", [
        ("language", "str"), ("entropy1000", "nat"), ("caseMutualInformation1000", "nat")]),
    "clauses": ("Clause", [
        ("textType", "enum"), ("source", "str"), ("order", "enum"), ("objectLength", "nat"),
        ("animate", "bool")]),
}


def lit(value, kind: str) -> str:
    if kind == "str":
        return json.dumps(value)
    if kind == "nat":
        return str(int(value))
    if kind == "enum":
        return f".{value}"
    if kind == "bool":
        return "true" if value else "false"
    raise ValueError(kind)


def row_lit(r: dict, fields) -> str:
    return "⟨" + ", ".join(lit(r[k], kind) for k, kind in fields) + "⟩"


def render_table(key: str, table: dict) -> str:
    ty, fields = TABLES[key]
    rows = table["rows"]
    lits = ",\n   ".join(row_lit(r, fields) for r in rows)
    doc = textwrap.fill(f"{table['description']} ({len(rows)} rows; {table['locator']}.)", 96)
    return f"/-- {doc} -/\ndef {key} : List {ty} :=\n  [{lits}]\n"


def render(paper: str, doc: dict) -> str:
    meta = doc["meta"]
    tables = "\n".join(render_table(k, doc[k]) for k in TABLES if k in doc)
    return f"""import Linglib.Data.WordOrder.Corpus.Schema

/-!
# {paper} — corpus word-order data (generated)
[{meta['bibkey']}]

Auto-generated from `Linglib/Data/WordOrder/Corpus/{paper}.json` by
`scripts/gen_word_order_corpus.py`. **Do not edit by hand** — edit the JSON and re-run the
generator.

{textwrap.fill(meta['description'], 96)}
-/

namespace Data.WordOrder.Corpus.{paper}

{tables}
end Data.WordOrder.Corpus.{paper}
"""


def process(paper: str, check: bool) -> bool:
    json_path = DATA_DIR / f"{paper}.json"
    if not json_path.exists():
        sys.stderr.write(f"FATAL: JSON not found at {json_path.relative_to(ROOT)}\n")
        sys.exit(1)
    doc = json.loads(json_path.read_text(encoding="utf-8"))
    content = render(paper, doc)
    out = DATA_DIR / f"{paper}.lean"
    n = sum(len(doc[k]["rows"]) for k in TABLES if k in doc)
    if check:
        cur = out.read_text(encoding="utf-8") if out.exists() else ""
        if cur != content:
            sys.stderr.write(f"[check] DRIFT: {out.relative_to(ROOT)} out of sync with JSON\n")
            return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync ({n} rows)\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {json_path.relative_to(ROOT)} ({n} rows)\n")
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
