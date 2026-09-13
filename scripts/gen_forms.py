#!/usr/bin/env python3
"""Generate Lean 4 CLDF form modules from per-paper JSON files.

Usage:
    python3 scripts/gen_forms.py <AuthorYear>
    python3 scripts/gen_forms.py --all                # regenerate every paper
    python3 scripts/gen_forms.py --check [<AuthorYear>]  # verify sync, no writes
    python3 scripts/gen_forms.py --fmt [<AuthorYear>]    # canonical JSON format

Reads   Linglib/Data/Forms/<AuthorYear>.json
Writes  Linglib/Data/Forms/<AuthorYear>.lean, a standalone auto-generated
module declaring `namespace <AuthorYear>.Forms`.

JSON file format: an object whose keys are CLDF table names, each holding an
array of rows keyed by the CLDF column names:

  {
    "FormTable": [
      {"ID": "booij2019_xabbaaz", "Language_ID": "nort3139",
       "Parameter_ID": "baker", "Form": "xabbaaz",
       "Segments": ["x", "a", "b", "b", "aa", "z"],
       "Comment": "", "Source": ["booij-2019[(1)]"]}
    ],
    "ParameterTable": [
      {"ID": "baker", "Name": "baker", "Description": ""}
    ],
    "FormRelationTable": [                 // linglib extension, optional
      {"ID": "booij2019_kibiir_akbar", "Form_ID": "booij2019_kibiir",
       "Target_ID": "booij2019_akbar", "Relation": "comparative",
       "Source": ["booij-2019[(15)]"]}
    ]
  }

`Source` entries use the CLDF reference syntax `bibkey[label]`; a bare
`bibkey` is accepted with an empty label. Any further key of a `FormTable`
row is a CLDF custom column and is emitted, with its string value, into the
form's `columns` list in the order given.

Behavior mirrors scripts/gen_examples.py: errors out on malformed input,
idempotent, `--check` exits 1 on drift, `--fmt` rewrites JSON canonically
and refuses to write if the data would change. The `Linglib.lean` root
import is not touched.
"""

import json
import re
import sys
from pathlib import Path

ROOT     = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "Linglib" / "Data" / "Forms"

TABLES = ["FormTable", "ParameterTable", "FormRelationTable"]
FORM_KEYS = ["ID", "Language_ID", "Parameter_ID", "Form", "Segments", "Comment", "Source"]
PARAM_KEYS = ["ID", "Name", "Description"]
REL_KEYS = ["ID", "Form_ID", "Target_ID", "Relation", "Source"]

SOURCE_RE = re.compile(r"^\s*([^\[\]\s]+)\s*(?:\[(.*)\])?\s*$")
ID_RE = re.compile(r"^[a-zA-Z0-9_\-]+$")  # CLDF 1.3 `id` format


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_identifier(row_id: str, author_year_lower: str) -> str:
    prefix = author_year_lower + "_"
    local = row_id[len(prefix):] if row_id.lower().startswith(prefix) else row_id
    local = "".join(c if c.isalnum() or c == "_" else "_" for c in local)
    if not local or not local[0].isalpha():
        local = "f_" + local
    return local


def req(row: dict, key: str, where: str) -> str:
    v = row.get(key)
    if not isinstance(v, str) or not v.strip():
        raise ValueError(f"{where}: {key} is required and non-empty")
    return v.strip()


def req_id(row: dict, key: str, where: str) -> str:
    v = req(row, key, where)
    if not ID_RE.match(v):
        raise ValueError(f"{where}: {key} {v!r} violates the CLDF id format [a-zA-Z0-9_-]+")
    return v


def opt(row: dict, key: str) -> str:
    v = row.get(key)
    return v if isinstance(v, str) else ""


def emit_sources(xs, where: str, indent: str) -> str:
    """Emit a `List SourceRef` with each reference on its own line, so the
    bracketed bibkeys are not mistaken for `[key]` citations."""
    if xs is None:
        return "[]"
    if not isinstance(xs, list) or not all(isinstance(x, str) for x in xs):
        raise ValueError(f"{where}: Source must be a list of strings")
    items = []
    for x in xs:
        m = SOURCE_RE.match(x)
        if not m:
            raise ValueError(f"{where}: bad Source reference {x!r}; expected bibkey[label]")
        items.append(f"⟨{lean_string(m.group(1))}, {lean_string(m.group(2) or '')}⟩")
    if not items:
        return "[]"
    return "[\n" + ",\n".join(indent + "  " + it for it in items) + "\n" + indent + "]"


def emit_segments(xs, where: str) -> str:
    if not isinstance(xs, list) or not xs or not all(isinstance(x, str) and x for x in xs):
        raise ValueError(f"{where}: Segments must be a non-empty list of non-empty strings")
    return "[" + ", ".join(lean_string(x) for x in xs) + "]"


def emit_columns(row: dict, where: str) -> str:
    """Emit the custom columns of a `FormTable` row as a `columns` field, or
    nothing when the row has none."""
    extra = [(k, v) for k, v in row.items() if k not in FORM_KEYS]
    for k, v in extra:
        if not isinstance(v, str):
            raise ValueError(f"{where}: custom column {k!r} must hold a string")
    if not extra:
        return ""
    items = ", ".join(f"({lean_string(k)}, {lean_string(v)})" for k, v in extra)
    return f"\n    columns := [{items}]"


def emit_form(row: dict, ay: str) -> tuple[str, str]:
    rid = req_id(row, "ID", "FormTable row")
    where = f"form {rid!r}"
    local = lean_identifier(rid, ay)
    text = f"""def {local} : Form :=
  {{ id := {lean_string(rid)}
    languageId := {lean_string(req(row, "Language_ID", where))}
    parameterId := {lean_string(req(row, "Parameter_ID", where))}
    form := {lean_string(req(row, "Form", where))}
    segments := {emit_segments(row.get("Segments"), where)}
    comment := {lean_string(opt(row, "Comment"))}
    source := {emit_sources(row.get("Source"), where, "    ")}{emit_columns(row, where)} }}"""
    return local, text


def emit_parameter(row: dict) -> str:
    rid = req_id(row, "ID", "ParameterTable row")
    where = f"parameter {rid!r}"
    return (f"  {{ id := {lean_string(rid)}, name := {lean_string(req(row, 'Name', where))}, "
            f"description := {lean_string(opt(row, 'Description'))} }}")


def emit_relation(row: dict) -> str:
    rid = req_id(row, "ID", "FormRelationTable row")
    where = f"relation {rid!r}"
    return (f"  {{ id := {lean_string(rid)}, formId := {lean_string(req(row, 'Form_ID', where))}, "
            f"targetId := {lean_string(req(row, 'Target_ID', where))}, "
            f"relation := {lean_string(req(row, 'Relation', where))}, "
            f"source := {emit_sources(row.get('Source'), where, '    ')} }}")


def emit_list(name: str, ty: str, items: list[str]) -> str:
    if not items:
        return f"def {name} : List {ty} := []"
    return f"def {name} : List {ty} :=\n" + ",\n".join(items) + "\n]"


def emit_module(author_year: str, data: dict) -> str:
    ay = author_year.lower()
    forms = data.get("FormTable") or []
    params = data.get("ParameterTable") or []
    rels = data.get("FormRelationTable") or []
    for t in data:
        if t not in TABLES:
            raise ValueError(f"unknown table {t!r}; expected one of {TABLES}")
    form_ids = {req_id(r, "ID", "FormTable row") for r in forms}
    param_ids = {req_id(r, "ID", "ParameterTable row") for r in params}
    for r in forms:
        if r.get("Parameter_ID") not in param_ids:
            raise ValueError(f"form {r.get('ID')!r}: Parameter_ID not in ParameterTable")
    for r in rels:
        for k in ("Form_ID", "Target_ID"):
            if r.get(k) not in form_ids:
                raise ValueError(f"relation {r.get('ID')!r}: {k} not in FormTable")
    locals_and_defs = [emit_form(r, ay) for r in forms]
    body = "\n\n".join(t for _, t in locals_and_defs)
    all_def = "def all : List Form := [" + ", ".join(l for l, _ in locals_and_defs) + "]"
    params_def = emit_list("parameters", "Parameter", [emit_parameter(r) for r in params])
    rels_def = emit_list("relations", "FormRelation", [emit_relation(r) for r in rels])
    if params:
        params_def = params_def.replace(":=\n", ":= [\n", 1)
    if rels:
        rels_def = rels_def.replace(":=\n", ":= [\n", 1)
    return f"""import Linglib.Data.Forms.Schema

/-!
# `{author_year}` — CLDF form data

Auto-generated from `Linglib/Data/Forms/{author_year}.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace {author_year}.Forms`.
-/

namespace {author_year}.Forms

open Data.Forms

{body}

{all_def}

{params_def}

{rels_def}

end {author_year}.Forms
"""


def load(author_year: str) -> dict:
    json_path = JSON_DIR / f"{author_year}.json"
    if not json_path.exists():
        sys.stderr.write(f"FATAL: JSON not found at {json_path.relative_to(ROOT)}\n")
        sys.exit(1)
    try:
        with open(json_path, encoding="utf-8") as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: invalid JSON: {e}\n")
        sys.exit(1)
    if not isinstance(data, dict):
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: top level must be an object of tables\n")
        sys.exit(1)
    return data


def process(author_year: str, check: bool) -> bool:
    data = load(author_year)
    json_path = JSON_DIR / f"{author_year}.json"
    try:
        module_text = emit_module(author_year, data)
    except ValueError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)
    module_path = JSON_DIR / f"{author_year}.lean"
    rel_module = module_path.relative_to(ROOT)
    in_sync = module_path.exists() and module_path.read_text(encoding="utf-8") == module_text
    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel_module} in sync\n")
        else:
            sys.stderr.write(f"[check] DRIFT: {rel_module}; run scripts/gen_forms.py {author_year}\n")
        return in_sync
    if in_sync:
        sys.stdout.write(f"[gen] {rel_module} unchanged\n")
    else:
        module_path.write_text(module_text, encoding="utf-8")
        n = len(data.get("FormTable") or [])
        sys.stdout.write(f"[gen] {rel_module} ← {json_path.relative_to(ROOT)} ({n} form{'s' if n != 1 else ''})\n")
    return True


def _j(v) -> str:
    return json.dumps(v, ensure_ascii=False)


def _fmt_row(row: dict, keys: list[str], indent: str) -> str:
    ks = [k for k in keys if k in row] + [k for k in row if k not in keys]
    return "{\n" + ",\n".join(f"{indent}  {_j(k)}: {_j(row[k])}" for k in ks) + f"\n{indent}}}"


def format_data(data: dict) -> str:
    keyorder = {"FormTable": FORM_KEYS, "ParameterTable": PARAM_KEYS, "FormRelationTable": REL_KEYS}
    tables = [t for t in TABLES if t in data] + [t for t in data if t not in TABLES]
    out = ["{"]
    for ti, t in enumerate(tables):
        rows = data[t]
        comma = "," if ti < len(tables) - 1 else ""
        if not rows:
            out.append(f"  {_j(t)}: []{comma}")
            continue
        out.append(f"  {_j(t)}: [")
        for ri, row in enumerate(rows):
            rc = "," if ri < len(rows) - 1 else ""
            out.append("    " + _fmt_row(row, keyorder.get(t, []), "    ") + rc)
        out.append(f"  ]{comma}")
    out.append("}")
    return "\n".join(out) + "\n"


def fmt(author_year: str) -> bool:
    data = load(author_year)
    json_path = JSON_DIR / f"{author_year}.json"
    text = format_data(data)
    if json.loads(text) != data:
        sys.stderr.write(f"[fmt] REFUSING {json_path.relative_to(ROOT)}: round-trip mismatch\n")
        return False
    if json_path.read_text(encoding="utf-8") == text:
        sys.stdout.write(f"[fmt] {json_path.relative_to(ROOT)} unchanged\n")
    else:
        json_path.write_text(text, encoding="utf-8")
        sys.stdout.write(f"[fmt] {json_path.relative_to(ROOT)} reformatted\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    do_fmt = "--fmt" in args
    args = [a for a in args if a not in ("--check", "--fmt")]
    if args == ["--all"] or (not args and (check or do_fmt)):
        papers = sorted(p.stem for p in JSON_DIR.glob("*.json"))
    elif len(args) == 1 and not args[0].startswith("-"):
        papers = [args[0]]
    else:
        sys.stderr.write(
            "Usage: python3 scripts/gen_forms.py <AuthorYear> | --all\n"
            "       python3 scripts/gen_forms.py --check [<AuthorYear>]\n"
            "       python3 scripts/gen_forms.py --fmt [<AuthorYear>]\n")
        sys.exit(1)
    if do_fmt:
        if not all([fmt(p) for p in papers]):
            sys.exit(1)
        return
    if not all([process(p, check) for p in papers]):
        sys.exit(1)


if __name__ == "__main__":
    main()
