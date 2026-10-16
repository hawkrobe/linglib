#!/usr/bin/env python3
"""Generate Lean 4 paradigm modules from per-paper JSON files.

Usage:
    python3 scripts/gen_paradigms.py <AuthorYear>
    python3 scripts/gen_paradigms.py --all            # regenerate every paper
    python3 scripts/gen_paradigms.py --check [<P>]    # verify sync, no writes

Reads   Linglib/Data/Paradigms/<AuthorYear>.json
Writes  Linglib/Data/Paradigms/<AuthorYear>.lean, declaring `namespace <AuthorYear>.Paradigms`.

JSON file format, the Paralex tables under Paralex column names plus one extension table:

  {
    "bibkey": "bobaljik-2012",
    "description": "...",
    "cells":   [{"cell_id": "comparative", "label": "comparative", "ud": "Degree=Cmp"}],
    "lexemes": [{"lexeme_id": "eng_good", "language_ID": "stan1293", "label": "good",
                 "meaning": "good"}],
    "forms":   [{"form_id": "eng_good_comparative", "lexeme": "eng_good",
                 "cell": "comparative", "analysed_orth_form": "bett-er",
                 "source": ["bobaljik-2012[Table 4.1]"]}],
    "root_classes": [{"classes_id": "eng_good", "lexeme": "eng_good",
                      "forms": ["eng_good_positive", ...],
                      "classes": {"positive": "A", "comparative": "B", "superlative": "B"},
                      "source": ["bobaljik-2012[p. 109]"], "cognates": "other Germanic"}]
  }

A cell's `ud` is its Universal Dependencies features in the CoNLL-U syntax (`Case=Nom|Number=Sing`),
checked against the constructors of `Linglib/Data/UD/Features.lean`. A form's Lean `form` is its
`analysed_orth_form` without hyphens. `comment` (any table) and `cognates` are validated and not
emitted. The generator rejects malformed input, unknown keys, dangling references and unknown
bibkeys; it is idempotent, and `--check` exits 1 on drift.
"""

import json
import re
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_module_frontier import as_module_if_possible  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "Linglib" / "Data" / "Paradigms"
UD_FEATURES = ROOT / "Linglib" / "Data" / "UD" / "Features.lean"
BIB = ROOT / "references.bib"

ID_RE = re.compile(r"^[a-z][a-z0-9_]*$")
GLOTTO_RE = re.compile(r"^[a-z0-9]{4}[0-9]{4}$")
SOURCE_RE = re.compile(r"^\s*([^\[\]\s]+)\s*(?:\[(.*)\])?\s*$")

# UD feature -> (`UD.MorphFeatures` field, `UD` type). `Reflex` is a Bool field, not listed.
FEATURES = {"Number": ("number", "Number"), "Gender": ("gender", "Gender"),
            "Case": ("case_", "Case"), "Definite": ("definite", "Definite"),
            "Degree": ("degree", "Degree"), "PronType": ("pronType", "PronType"),
            "Person": ("person", "Person"), "VerbForm": ("verbForm", "VerbForm"),
            "Tense": ("tense", "Tense"), "Aspect": ("aspect", "Aspect"), "Mood": ("mood", "Mood"),
            "Voice": ("voice", "Voice"), "Polarity": ("polarity", "Polarity")}
PERSON = {"0": "zero", "1": "first", "2": "second", "3": "third"}

TABLES = {"cells": {"cell_id", "label", "ud", "comment"},
          "lexemes": {"lexeme_id", "language_ID", "label", "meaning", "comment"},
          "forms": {"form_id", "lexeme", "cell", "analysed_orth_form", "source", "comment"},
          "root_classes": {"classes_id", "lexeme", "forms", "classes", "source", "cognates",
                           "comment"}}


def fail(msg: str):
    raise ValueError(msg)


def ud_constructors() -> dict[str, set[str]]:
    """The constructors of each inductive of `Data/UD/Features.lean`."""
    ctors, current = {}, None
    for line in UD_FEATURES.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^inductive (\w+) where", line)
        if m:
            current = m.group(1)
            ctors[current] = set()
            continue
        m = re.match(r"^\s*\|\s*(\w+)", line)
        if m and current:
            ctors[current].add(m.group(1))
        elif line.strip() and not line.startswith(" ") and not line.startswith("--"):
            current = None
    return ctors


def bibkeys() -> set[str]:
    return set(re.findall(r"^@\w+\{([^,]+),", BIB.read_text(encoding="utf-8"), re.M))


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def check_keys(row: dict, table: str, where: str):
    extra = set(row) - TABLES[table]
    if extra:
        fail(f"{where}: unknown keys {sorted(extra)}")
    for k in ("comment", "cognates"):
        if k in row and not isinstance(row[k], str):
            fail(f"{where}: {k} must be a string")


def req(row: dict, key: str, where: str) -> str:
    v = row.get(key)
    if not isinstance(v, str) or not v.strip():
        fail(f"{where}: {key} is required and non-empty")
    return v


def req_id(row: dict, key: str, where: str) -> str:
    v = req(row, key, where)
    if not ID_RE.match(v):
        fail(f"{where}: {key} {v!r} must match [a-z][a-z0-9_]*")
    return v


def emit_cell(ud: str, ctors: dict[str, set[str]], where: str) -> str:
    fields = []
    for feat in ud.split("|"):
        name, _, value = feat.partition("=")
        if name not in FEATURES:
            fail(f"{where}: unknown UD feature {name!r}")
        field, ty = FEATURES[name]
        ctor = PERSON.get(value) if name == "Person" else value
        if ctor not in ctors.get(ty, set()):
            fail(f"{where}: {name}={value} is not a constructor of UD.{ty}")
        fields.append(f"{field} := ↑UD.{ty}.{ctor}")
    return "{ " + ", ".join(fields) + " }"


def emit_sources(xs, keys: set[str], where: str) -> str:
    """A `List SourceRef`, each reference on its own line so that the bracketed bibkeys are not
    mistaken for `[key]` citations."""
    if not isinstance(xs, list) or not xs or not all(isinstance(x, str) for x in xs):
        fail(f"{where}: source must be a non-empty list of strings")
    out = []
    for x in xs:
        m = SOURCE_RE.match(x)
        if not m:
            fail(f"{where}: bad source {x!r}; expected bibkey[locator]")
        if m.group(1) not in keys:
            fail(f"{where}: bibkey {m.group(1)!r} is not in references.bib")
        out.append(f"⟨{lean_string(m.group(1))}, {lean_string(m.group(2) or '')}⟩")
    return "[\n      " + ",\n      ".join(out) + "\n    ]"


def emit_module(paper: str, data: dict) -> str:
    unknown = set(data) - set(TABLES) - {"bibkey", "description"}
    if unknown:
        fail(f"unknown top-level keys {sorted(unknown)}")
    keys = bibkeys()
    if data.get("bibkey") not in keys:
        fail(f"bibkey {data.get('bibkey')!r} is not in references.bib")
    ctors = ud_constructors()
    out = []

    cells = {}
    for r in data.get("cells") or []:
        where = f"cell {r.get('cell_id')!r}"
        check_keys(r, "cells", where)
        cid = req_id(r, "cell_id", where)
        req(r, "label", where)
        cells[cid] = r
        out.append(f"/-- The {r['label']} cell, `{r['ud']}`. -/\n"
                   f"def {cid} : UD.MorphFeatures := {emit_cell(req(r, 'ud', where), ctors, where)}")

    lexemes = {}
    for r in data.get("lexemes") or []:
        where = f"lexeme {r.get('lexeme_id')!r}"
        check_keys(r, "lexemes", where)
        lid = req_id(r, "lexeme_id", where)
        if lid in lexemes or lid in cells:
            fail(f"{where}: duplicate identifier")
        g = req(r, "language_ID", where)
        if not GLOTTO_RE.match(g):
            fail(f"{where}: language_ID {g!r} is not a Glottocode")
        lexemes[lid] = r
        out.append(f"def {lid} : Lexeme :=\n  {{ id := {lean_string(lid)}, languageId := {lean_string(g)}, "
                   f"label := {lean_string(req(r, 'label', where))}, "
                   f"meaning := {lean_string(req(r, 'meaning', where))} }}")

    forms = {}
    for r in data.get("forms") or []:
        where = f"form {r.get('form_id')!r}"
        check_keys(r, "forms", where)
        fid = req_id(r, "form_id", where)
        if fid in forms or fid in lexemes or fid in cells:
            fail(f"{where}: duplicate identifier")
        lx, cell = req(r, "lexeme", where), req(r, "cell", where)
        if lx not in lexemes:
            fail(f"{where}: lexeme {lx!r} not in lexemes")
        if cell not in cells:
            fail(f"{where}: cell {cell!r} not in cells")
        a = req(r, "analysed_orth_form", where)
        forms[fid] = r
        out.append(f"def {fid} : Form :=\n  {{ id := {lean_string(fid)}, lexeme := {lx}, cell := {cell}, "
                   f"form := {lean_string(a.replace('-', ''))},\n    analysed := {lean_string(a)}, "
                   f"source := {emit_sources(r.get('source'), keys, where)} }}")

    classes = []
    for r in data.get("root_classes") or []:
        where = f"root classes {r.get('classes_id')!r}"
        check_keys(r, "root_classes", where)
        cid = req_id(r, "classes_id", where)
        if cid in classes:
            fail(f"{where}: duplicate identifier")
        lx = req(r, "lexeme", where)
        if lx not in lexemes:
            fail(f"{where}: lexeme {lx!r} not in lexemes")
        fs = r.get("forms")
        if not isinstance(fs, list) or not fs:
            fail(f"{where}: forms must be a non-empty list")
        for f in fs:
            if f not in forms:
                fail(f"{where}: form {f!r} not in forms")
            if forms[f]["lexeme"] != lx:
                fail(f"{where}: form {f!r} is not a form of {lx!r}")
        cls = r.get("classes")
        if not isinstance(cls, dict) or not cls:
            fail(f"{where}: classes must be a non-empty object from cells to letters")
        pairs = []
        for c, letter in cls.items():
            if c not in cells:
                fail(f"{where}: cell {c!r} not in cells")
            if not (isinstance(letter, str) and re.fullmatch(r"[A-Z]", letter)):
                fail(f"{where}: class of {c!r} must be one capital letter")
            pairs.append(f"({c}, {ord(letter) - ord('A')})")
        for f in fs:
            if forms[f]["cell"] not in cls:
                fail(f"{where}: form {f!r} is in a cell with no class")
        classes.append(cid)
        out.append(f"def {cid}.roots : RootClasses :=\n  {{ id := {lean_string(cid)}, lexeme := {lx}, "
                   f"forms := [{', '.join(fs)}],\n    classes := [{', '.join(pairs)}],\n    "
                   f"source := {emit_sources(r.get('source'), keys, where)} }}")

    lists = [f"/-- Every lexeme of the data. -/\ndef lexemes : List Lexeme := [{', '.join(lexemes)}]",
             f"/-- Every form of the data. -/\ndef forms : List Form := [{', '.join(forms)}]",
             f"/-- Every root-class judgment of the data. -/\n"
             f"def rootClasses : List RootClasses := [{', '.join(c + '.roots' for c in classes)}]"]
    body = "\n\n".join(out + lists)
    return f"""import Linglib.Data.Paradigms.Schema

/-!
# `{paper}`: paradigm data

Auto-generated from `Linglib/Data/Paradigms/{paper}.json` by `scripts/gen_paradigms.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in
`namespace {paper}.Paradigms`.
-/

namespace {paper}.Paradigms

open Data.Paradigms

{body}

end {paper}.Paradigms
"""


def process(paper: str, check: bool) -> bool:
    path = JSON_DIR / f"{paper}.json"
    if not path.exists():
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)} not found\n")
        sys.exit(1)
    try:
        text = as_module_if_possible(emit_module(paper, json.loads(path.read_text(encoding="utf-8"))))
    except (ValueError, json.JSONDecodeError) as e:
        sys.stderr.write(f"FATAL: {path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)
    target = JSON_DIR / f"{paper}.lean"
    in_sync = target.exists() and target.read_text(encoding="utf-8") == text
    rel = target.relative_to(ROOT)
    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel} in sync\n")
        else:
            sys.stderr.write(f"[check] DRIFT: {rel}; run scripts/gen_paradigms.py {paper}\n")
        return in_sync
    if not in_sync:
        target.write_text(text, encoding="utf-8")
    sys.stdout.write(f"[gen] {rel} {'unchanged' if in_sync else 'written'}\n")
    return True


def main():
    args = sys.argv[1:]
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    if args == ["--all"] or (not args and check):
        papers = sorted(p.stem for p in JSON_DIR.glob("*.json"))
    elif len(args) == 1 and not args[0].startswith("-"):
        papers = args
    else:
        sys.stderr.write(__doc__)
        sys.exit(1)
    if not all([process(p, check) for p in papers]):
        sys.exit(1)


if __name__ == "__main__":
    main()
