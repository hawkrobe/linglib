#!/usr/bin/env python3
"""Generate typed experimental-result modules from canonical per-paper JSON.

A paper's experimental results are canonical JSON at
`Linglib/Data/Experiments/<Paper>.json`; this emits the typed Lean module
`Linglib/Data/Experiments/<Paper>.lean` (namespace `Data.Experiments.<Paper>`).
The generated Lean is never hand-edited: edit the JSON and re-run.

A JSON file has four parts:

* `meta`: `bibkey` (a `references.bib` key) and `description`.
* `types`: the paper's own coding labels, each emitted as an enum. A level has a
  Lean `name`, the `label` the paper prints, and a `doc`.
* `constants`: design values the paper states once (`nat`, `decimal`).
* `tables`: one per printed table, emitted as a structure and a list of rows in the
  paper's order. A table has a `name`, a `structure` name, a `doc`, a `locator`, a
  `verified` status (`page-image`, `text-layer` or `unverified`), its `columns`
  and its `rows`. A row may carry a `note`, emitted as a comment.

Column types form a closed vocabulary:

* `nat`, `int`
* `decimal`: a JSON string as printed ("99.1", "75", "0"), emitted as
  `Data.Experiments.Decimal`
* `<Type>`: a level of a declared type, written by its label
* `literals <Type>`: a signed feature list in the paper's notation,
  "[+IHCr, -Mediation]", emitted as `List (<Type> × Sign)`
* `option <T>`, `list <T>` for any of the above (`null` is `none`)

    python3 scripts/gen_experiments.py Hafeez2025       # (re)generate
    python3 scripts/gen_experiments.py --check [<P>]    # verify, no writes (CI)
    python3 scripts/gen_experiments.py --all            # every JSON
"""
import json
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "Linglib" / "Data" / "Experiments"
BIB = ROOT / "references.bib"
VERIFIED = {"page-image": "checked against the page images",
            "text-layer": "checked against the PDF text layer only",
            "unverified": "not yet checked against the source"}
IDENT = re.compile(r"^[a-z][A-Za-z0-9]*$")
TYPE_IDENT = re.compile(r"^[A-Z][A-Za-z0-9]*$")
DECIMAL = re.compile(r"^(-?)(\d+)(?:\.(\d+))?$")
LITERAL = re.compile(r"^([+-])\s*(\S+)$")


def fatal(where: str, msg: str):
    sys.stderr.write(f"FATAL: {where}: {msg}\n")
    sys.exit(1)


class Types:
    def __init__(self, types: list, where: str):
        self.levels = {}
        for i, t in enumerate(types):
            w = f"{where}.types[{i}]"
            if not TYPE_IDENT.match(t.get("name", "")):
                fatal(w, f"type name {t.get('name')!r} is not an UpperCamel identifier")
            by_label = {}
            for j, lv in enumerate(t["levels"]):
                if not IDENT.match(lv["name"]):
                    fatal(f"{w}.levels[{j}]", f"level name {lv['name']!r} is not lowerCamel")
                if lv["label"] in by_label or lv["name"] in by_label.values():
                    fatal(f"{w}.levels[{j}]", f"duplicate level {lv['label']!r}")
                by_label[lv["label"]] = lv["name"]
            self.levels[t["name"]] = by_label

    def level(self, ty: str, label, where: str) -> str:
        if not isinstance(label, str) or label not in self.levels[ty]:
            fatal(where, f"{label!r} is not a level of {ty}")
        return f".{self.levels[ty][label]}"


def parse_type(s: str, types: Types, where: str):
    parts = s.split()
    if parts[0] in ("option", "list") and len(parts) > 1:
        return (parts[0], parse_type(" ".join(parts[1:]), types, where))
    if parts[0] == "literals" and len(parts) == 2 and parts[1] in types.levels:
        return ("literals", parts[1])
    if len(parts) == 1 and parts[0] in ("nat", "int", "decimal"):
        return (parts[0],)
    if len(parts) == 1 and parts[0] in types.levels:
        return ("enum", parts[0])
    fatal(where, f"unknown column type {s!r}")


def lean_type(t) -> str:
    match t[0]:
        case "nat": return "ℕ"
        case "int": return "ℤ"
        case "decimal": return "Decimal"
        case "enum": return t[1]
        case "literals": return f"List ({t[1]} × Sign)"
        case "option": return f"Option {paren(lean_type(t[1]))}"
        case "list": return f"List {paren(lean_type(t[1]))}"


def decimal_lit(v, where: str) -> str:
    m = DECIMAL.match(v) if isinstance(v, str) else None
    if not m:
        fatal(where, f"decimal {v!r} is not a printed decimal string")
    sign, whole, frac = m.group(1), m.group(2), m.group(3) or ""
    return f"⟨{sign}{int(whole + frac)}, {len(frac)}⟩"


def literals_lit(v, ty: str, types: Types, where: str) -> str:
    if not (isinstance(v, str) and v.startswith("[") and v.endswith("]")):
        fatal(where, f"{v!r} is not a bracketed literal list")
    items, seen = [], set()
    for part in filter(None, (p.strip() for p in v[1:-1].split(","))):
        m = LITERAL.match(part)
        if not m:
            fatal(where, f"{part!r} is not a signed feature")
        if m.group(2) in seen:
            fatal(where, f"feature {m.group(2)!r} repeats")
        seen.add(m.group(2))
        sign = ".plus" if m.group(1) == "+" else ".minus"
        items.append(f"({types.level(ty, m.group(2), where)}, {sign})")
    return "[" + ", ".join(items) + "]"


def value_lit(v, t, types: Types, where: str) -> str:
    match t[0]:
        case "nat":
            if not (isinstance(v, int) and v >= 0):
                fatal(where, f"{v!r} is not a natural number")
            return str(v)
        case "int":
            if not isinstance(v, int):
                fatal(where, f"{v!r} is not an integer")
            return str(v)
        case "decimal": return decimal_lit(v, where)
        case "enum": return types.level(t[1], v, where)
        case "literals": return literals_lit(v, t[1], types, where)
        case "option":
            return "none" if v is None else f"some {paren(value_lit(v, t[1], types, where))}"
        case "list":
            if not isinstance(v, list):
                fatal(where, f"{v!r} is not a list")
            return "[" + ", ".join(value_lit(x, t[1], types, f"{where}[{i}]")
                                   for i, x in enumerate(v)) + "]"


def paren(s: str) -> str:
    return f"({s})" if " " in s and not s.startswith(("[", "⟨", "(")) else s


def wrap_field(f: str, end: str, indent: str = "     ") -> list:
    """A field of a wrapped row on its own line, or a long list one element per line."""
    if len(indent) + len(f) + len(end) <= 100 or not f.startswith("["):
        return [f"{indent}{f}{end}"]
    elems, depth, start = [], 0, 1
    for i, ch in enumerate(f):
        if ch in "[(⟨":
            depth += 1
        elif ch in "])⟩":
            depth -= 1
        elif ch == "," and depth == 1:
            elems.append(f[start:i].strip())
            start = i + 1
    elems.append(f[start:-1].strip())
    lines = [f"{indent}[{elems[0]},"]
    lines += [f"{indent} {e}," for e in elems[1:-1]]
    lines.append(f"{indent} {elems[-1]}]{end}")
    return lines


def doc(text: str, indent: str = "") -> str:
    body = textwrap.fill(text, 100 - len(indent) - 4, subsequent_indent=indent)
    return f"{indent}/-- {body} -/"


def render_enum(t: dict) -> str:
    lines = [doc(t["doc"]), f"inductive {t['name']} where"]
    for lv in t["levels"]:
        lines.append(doc(f"{lv['label']}: {lv['doc']}", "  "))
        lines.append(f"  | {lv['name']}")
    lines.append("  deriving DecidableEq, Repr, Fintype")
    return "\n".join(lines)


def render_constant(c: dict, types: Types, where: str) -> str:
    t = parse_type(c["type"], types, where)
    status = VERIFIED.get(c.get("verified"))
    if status is None or not c.get("locator"):
        fatal(where, "a constant needs a locator and a verified status")
    return (doc(f"{c['doc']} ({c['locator']}; {status}.)") + "\n"
            + f"def {c['name']} : {lean_type(t)} := {value_lit(c['value'], t, types, where)}")


def render_table(tb: dict, types: Types, where: str) -> str:
    status = VERIFIED.get(tb.get("verified"))
    if status is None or not tb.get("locator"):
        fatal(where, "a table needs a locator and a verified status")
    cols = [(c["name"], parse_type(c["type"], types, f"{where}.columns[{i}]"), c["doc"])
            for i, c in enumerate(tb["columns"])]
    names = [n for n, _, _ in cols]
    struct = [doc(f"A row of {tb['locator']}: {tb['doc']}"), f"structure {tb['structure']} where"]
    for n, t, d in cols:
        struct += [doc(d, "  "), f"  {n} : {lean_type(t)}"]
    struct.append("  deriving DecidableEq, Repr")
    rows = []
    for i, r in enumerate(tb["rows"]):
        w = f"{where}.rows[{i}]"
        extra = set(r) - set(names) - {"note"}
        missing = set(names) - set(r)
        if extra or missing:
            fatal(w, f"columns missing {sorted(missing)}, undeclared {sorted(extra)}")
        rows.append(([value_lit(r[n], t, types, f"{w}.{n}") for n, t, _ in cols], r.get("note")))
    body = []
    for i, (fields, note) in enumerate(rows):
        lead = "  [" if i == 0 else "   "
        sep = "," if i < len(rows) - 1 else "]"
        comment = f"  -- {note}" if note else ""
        line = f"{lead}⟨{', '.join(fields)}⟩{sep}"
        if len(line) + len(comment) <= 100:
            body.append(line + comment)
        else:
            body.append(f"{lead}⟨{fields[0]},{comment}")
            for j, f in enumerate(fields[1:], 1):
                end = "," if j < len(fields) - 1 else f"⟩{sep}"
                body += wrap_field(f, end)
    defn = [doc(f"The {len(rows)} rows of {tb['locator']}, in the paper's order; {status}."),
            f"def {tb['name']} : List {tb['structure']} :=", *body]
    return "\n".join(struct) + "\n\n" + "\n".join(defn)


def bibkeys() -> set:
    return set(re.findall(r"^@\w+\{([^,\s]+),", BIB.read_text(encoding="utf-8"), re.M))


def render(paper: str, d: dict) -> str:
    meta = d["meta"]
    if meta.get("bibkey") not in bibkeys():
        fatal(f"{paper}.meta", f"bibkey {meta.get('bibkey')!r} not in references.bib")
    types = Types(d.get("types", []), paper)
    parts = [render_enum(t) for t in d.get("types", [])]
    parts += [render_constant(c, types, f"{paper}.constants[{i}]")
              for i, c in enumerate(d.get("constants", []))]
    parts += [render_table(tb, types, f"{paper}.tables[{i}]")
              for i, tb in enumerate(d.get("tables", []))]
    desc = textwrap.fill(meta["description"], 100)
    body = "\n\n".join(parts)
    return f"""module

public import Linglib.Data.Experiments.Schema

/-!
# {paper}: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/{paper}.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

{desc}

## References

* [{meta['bibkey']}]
-/

@[expose] public section

namespace Data.Experiments.{paper}

{body}

end Data.Experiments.{paper}
"""


def process(paper: str, check: bool) -> bool:
    src = DATA_DIR / f"{paper}.json"
    if not src.exists():
        fatal(paper, f"JSON not found at {src.relative_to(ROOT)}")
    content = render(paper, json.loads(src.read_text(encoding="utf-8")))
    out = DATA_DIR / f"{paper}.lean"
    if check:
        if not out.exists() or out.read_text(encoding="utf-8") != content:
            sys.stderr.write(f"[check] DRIFT: {out.relative_to(ROOT)} out of sync with JSON\n")
            return False
        sys.stdout.write(f"[check] {out.relative_to(ROOT)} in sync\n")
        return True
    out.write_text(content, encoding="utf-8")
    sys.stdout.write(f"[gen] {out.relative_to(ROOT)} ← {src.relative_to(ROOT)}\n")
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
    sys.exit(0 if all([process(p, check) for p in papers]) else 1)


if __name__ == "__main__":
    main()
