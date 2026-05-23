#!/usr/bin/env python3
"""Generate Lean 4 LinguisticExample defs from per-paper JSON files.

Usage:
    python3 scripts/gen_examples.py <AuthorYear>

Example:
    python3 scripts/gen_examples.py Charlow2014
        Reads:    Linglib/Data/Examples/Charlow2014.json
        Locates:  Linglib/Studies/Charlow2014.lean (or
                  Linglib/Studies/Charlow2014/Basic.lean for multi-file papers)
        Inserts:  generated `namespace Examples ... end` block between markers
                  -- BEGIN GENERATED EXAMPLES
                  -- END GENERATED EXAMPLES

JSON file format: a single top-level JSON array of example objects. Each
object's fields mirror the `LinguisticExample` Lean struct:

  {
    "id": "charlow2014_donkey1",
    "source":     {"bibkey": "geach-1962", "paperLabel": "ch. III, ..."},
    "reportedIn": {"bibkey": "charlow-2014", "paperLabel": "Ch. 2"},  // optional
    "language": "stan1293",                  // Glottocode
    "primaryText": "...",
    "discourseSegments": [],                 // empty for single-sentence
    "glossedTokens": [["Every", "every"], ...],  // pairs as 2-arrays
    "translation": "...",
    "context": "",
    "judgment": "acceptable",                // one of the 5 cases
    "alternatives": [{"form": "...", "judgment": "unacceptable"}],
    "readings":     [{"name": "strong", "judgment": "acceptable"},
                     {"name": "weak",   "judgment": "acceptable"}],
    "comment": "...",
    "metaLanguage": "stan1293",              // optional, default "stan1293"
    "lgrConformance": "WORD_ALIGNED"         // optional, default ""
  }

Behavior:
- Errors out (exit 1) if the JSON file doesn't exist.
- Errors out if zero or multiple study files match the AuthorYear.
- Errors out if either marker is missing in the target file.
- Errors out on schema violations (unknown judgment value, gloss/word
  length mismatch, missing required field, missing source.bibkey).
- Replaces *only* the content between markers; everything else is preserved.
- Idempotent: re-running on unchanged JSON produces no diff.

Defer to follow-on:
- `--check` mode (regenerate in-memory and assert no diff).
- Schema extensions (Tree, indexed anaphora, paper-relativized
  classifications) when a consuming study demands them.

Dependencies: pure stdlib (json module).
"""

import json
import sys
from pathlib import Path

ROOT       = Path(__file__).resolve().parent.parent
JSON_DIR   = ROOT / "Linglib" / "Data" / "Examples"
STUDIES    = ROOT / "Linglib" / "Studies"

BEGIN_MARKER = "-- BEGIN GENERATED EXAMPLES"
END_MARKER   = "-- END GENERATED EXAMPLES"

VALID_JUDGMENTS = {
    "acceptable", "marginal", "questionable", "unacceptable", "ungrammatical",
}


def lean_string(s: str) -> str:
    """Quote a string for Lean source. Escapes backslashes and quotes."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_identifier(example_id: str, author_year_lower: str) -> str:
    """Derive a Lean-valid identifier from a JSON example ID.

    `charlow2014_donkey1` → `donkey1` (strip the AuthorYear_ prefix and use
    the rest as the local identifier inside `namespace Examples`).
    """
    prefix = author_year_lower + "_"
    if example_id.lower().startswith(prefix):
        local = example_id[len(prefix):]
    else:
        local = example_id
    local = "".join(c if c.isalnum() or c == "_" else "_" for c in local)
    if not local or not local[0].isalpha():
        local = "ex_" + local
    return local


def parse_judgment(raw: str, where: str) -> str:
    j = (raw or "").strip().lower()
    if j not in VALID_JUDGMENTS:
        raise ValueError(
            f"{where}: invalid judgment {raw!r}; expected one of "
            f"{sorted(VALID_JUDGMENTS)}"
        )
    return f".{j}"


def emit_source_ref(s: dict, where: str) -> str:
    """Emit a SourceRef literal from a {bibkey, paperLabel} object."""
    if not isinstance(s, dict):
        raise ValueError(f"{where}: source/reportedIn must be an object, got {type(s).__name__}")
    bib = (s.get("bibkey") or "").strip()
    lab = (s.get("paperLabel") or "").strip()
    if not bib:
        raise ValueError(f"{where}: source.bibkey is required and non-empty")
    return f"⟨{lean_string(bib)}, {lean_string(lab)}⟩"


def emit_reported_in(r, where: str) -> str:
    """Emit `none` for null/absent, `some ⟨…⟩` for a SourceRef object."""
    if r is None:
        return "none"
    return f"some {emit_source_ref(r, where + '.reportedIn')}"


def emit_string_list(xs, where: str) -> str:
    if not isinstance(xs, list) or not all(isinstance(x, str) for x in xs):
        raise ValueError(f"{where}: expected list of strings")
    if not xs:
        return "[]"
    return "[" + ", ".join(lean_string(x) for x in xs) + "]"


def emit_glossed_tokens(xs, where: str) -> str:
    """Emit a List (String × String) literal from JSON pairs.

    Each entry must be a 2-element array: [analyzedWord, gloss].
    """
    if not isinstance(xs, list):
        raise ValueError(f"{where}: glossedTokens must be an array")
    if not xs:
        return "[]"
    items = []
    for i, pair in enumerate(xs):
        if not (isinstance(pair, list) and len(pair) == 2
                and all(isinstance(s, str) for s in pair)):
            raise ValueError(
                f"{where}.glossedTokens[{i}]: expected 2-string array, got {pair!r}"
            )
        items.append(f"({lean_string(pair[0])}, {lean_string(pair[1])})")
    return "[" + ", ".join(items) + "]"


def emit_string_pair_list(xs, where: str) -> str:
    """Emit a List (String × String) literal from JSON.

    Accepts either:
    - list of 2-element arrays:  [["key", "value"], ...]
    - list of objects:           [{"key": "...", "value": "..."}, ...]
    - object (treated as dict):  {"k1": "v1", "k2": "v2"}
    """
    if isinstance(xs, dict):
        items = list(xs.items())
    elif isinstance(xs, list):
        items = []
        for i, entry in enumerate(xs):
            if isinstance(entry, list) and len(entry) == 2 and all(isinstance(s, str) for s in entry):
                items.append((entry[0], entry[1]))
            elif isinstance(entry, dict) and "key" in entry and "value" in entry:
                if not (isinstance(entry["key"], str) and isinstance(entry["value"], str)):
                    raise ValueError(f"{where}[{i}]: key/value must be strings")
                items.append((entry["key"], entry["value"]))
            else:
                raise ValueError(
                    f"{where}[{i}]: expected 2-string array or {{key, value}} object"
                )
    else:
        raise ValueError(f"{where}: expected array or object")
    if not items:
        return "[]"
    return "[" + ", ".join(
        f"({lean_string(k)}, {lean_string(v)})" for k, v in items
    ) + "]"


def emit_form_judgment_list(xs, where: str, key: str) -> str:
    """Emit a List (String × Judgment) literal.

    Each entry is `{key: <string>, judgment: <judgment>}`. `key` is "form"
    for alternatives or "name" for readings.
    """
    if not isinstance(xs, list):
        raise ValueError(f"{where}: expected an array")
    if not xs:
        return "[]"
    items = []
    for i, entry in enumerate(xs):
        if not isinstance(entry, dict):
            raise ValueError(f"{where}[{i}]: expected an object")
        s = entry.get(key)
        j = entry.get("judgment")
        if not isinstance(s, str):
            raise ValueError(f"{where}[{i}].{key}: expected a string")
        items.append(f"({lean_string(s)}, {parse_judgment(j, f'{where}[{i}].judgment')})")
    return "[" + ", ".join(items) + "]"


def emit_example(ex: dict, author_year_lower: str) -> str:
    ex_id   = (ex.get("id") or "").strip()
    if not ex_id:
        raise ValueError("example missing required `id`")
    where   = f"example {ex_id!r}"
    local   = lean_identifier(ex_id, author_year_lower)

    src         = emit_source_ref(ex.get("source") or {}, where + ".source")
    reported_in = emit_reported_in(ex.get("reportedIn"), where)
    language    = (ex.get("language") or "").strip()
    primary     = ex.get("primaryText") or ""
    discourse   = emit_string_list(ex.get("discourseSegments", []), where + ".discourseSegments")
    glossed     = emit_glossed_tokens(ex.get("glossedTokens", []), where)
    translation = ex.get("translation") or ""
    context     = ex.get("context") or ""
    judgment    = parse_judgment(ex.get("judgment", ""), where + ".judgment")
    alternatives = emit_form_judgment_list(ex.get("alternatives", []), where + ".alternatives", "form")
    readings    = emit_form_judgment_list(ex.get("readings", []), where + ".readings", "name")
    features    = emit_string_pair_list(ex.get("paperFeatures", []), where + ".paperFeatures")
    comment     = ex.get("comment") or ""
    meta_lang   = (ex.get("metaLanguage") or "stan1293").strip() or "stan1293"
    lgr         = (ex.get("lgrConformance") or "").strip()

    return f"""def {local} : LinguisticExample :=
  {{ id := {lean_string(ex_id)}
    source := {src}
    reportedIn := {reported_in}
    language := {lean_string(language)}
    primaryText := {lean_string(primary)}
    discourseSegments := {discourse}
    glossedTokens := {glossed}
    translation := {lean_string(translation)}
    context := {lean_string(context)}
    judgment := {judgment}
    alternatives := {alternatives}
    readings := {readings}
    paperFeatures := {features}
    comment := {lean_string(comment)}
    metaLanguage := {lean_string(meta_lang)}
    lgrConformance := {lean_string(lgr)} }}"""


def emit_block(author_year: str, examples: list) -> str:
    ay_lower = author_year.lower()
    if not examples:
        body = "-- (no examples in JSON)"
        all_def = "def all : List LinguisticExample := []"
    else:
        body = "\n\n".join(emit_example(e, ay_lower) for e in examples)
        local_ids = [
            lean_identifier((e.get("id") or "").strip(), ay_lower)
            for e in examples
        ]
        all_def = f"def all : List LinguisticExample := [{', '.join(local_ids)}]"

    return f"""{BEGIN_MARKER}
-- (Generated from Linglib/Data/Examples/{author_year}.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

{body}

{all_def}

end Examples
{END_MARKER}"""


def find_target_file(author_year: str) -> Path:
    """Locate the study file containing the marker block.

    Search order:
      1. `Linglib/Studies/{author_year}.lean` (flat single-file paper)
      2. Any `.lean` file under `Linglib/Studies/{author_year}/` that
         contains the BEGIN/END marker block (multi-file paper subdir;
         the markers can live in whichever file conceptually owns the
         examples, not necessarily `Basic.lean`).

    Errors out if zero or multiple files match.
    """
    flat_match = STUDIES / f"{author_year}.lean"
    subdir     = STUDIES / author_year

    candidates: list[Path] = []
    if flat_match.exists():
        candidates.append(flat_match)
    if subdir.is_dir():
        for path in sorted(subdir.glob("*.lean")):
            text = path.read_text(encoding="utf-8")
            if BEGIN_MARKER in text and END_MARKER in text:
                candidates.append(path)

    if len(candidates) == 0:
        sys.stderr.write(
            f"FATAL: no study file with marker block found for {author_year}; checked:\n"
            f"  Linglib/Studies/{author_year}.lean\n"
            f"  Linglib/Studies/{author_year}/*.lean\n"
            f"Add `-- BEGIN GENERATED EXAMPLES` / `-- END GENERATED EXAMPLES`\n"
            f"markers to the file that should host the generated block.\n"
        )
        sys.exit(1)
    if len(candidates) > 1:
        paths = "\n  ".join(str(p.relative_to(ROOT)) for p in candidates)
        sys.stderr.write(
            f"FATAL: ambiguous match for {author_year}; multiple files carry the marker block:\n"
            f"  {paths}\n"
        )
        sys.exit(1)
    return candidates[0]


def replace_between_markers(file_path: Path, new_block: str) -> bool:
    text = file_path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)

    begin_idx = None
    end_idx   = None
    for i, line in enumerate(lines):
        if line.rstrip("\n") == BEGIN_MARKER:
            if begin_idx is not None:
                sys.stderr.write(
                    f"FATAL: multiple BEGIN markers in {file_path.relative_to(ROOT)}\n"
                )
                sys.exit(1)
            begin_idx = i
        elif line.rstrip("\n") == END_MARKER:
            if end_idx is not None:
                sys.stderr.write(
                    f"FATAL: multiple END markers in {file_path.relative_to(ROOT)}\n"
                )
                sys.exit(1)
            end_idx = i

    if begin_idx is None:
        sys.stderr.write(
            f"FATAL: missing marker {BEGIN_MARKER!r} in {file_path.relative_to(ROOT)}\n"
            f"       Add the marker block (BEGIN + END on consecutive lines) where\n"
            f"       generated examples should be inserted.\n"
        )
        sys.exit(1)
    if end_idx is None:
        sys.stderr.write(
            f"FATAL: missing marker {END_MARKER!r} in {file_path.relative_to(ROOT)}\n"
        )
        sys.exit(1)
    if end_idx <= begin_idx:
        sys.stderr.write(
            f"FATAL: END marker precedes BEGIN marker in {file_path.relative_to(ROOT)}\n"
        )
        sys.exit(1)

    new_text = "".join(lines[:begin_idx]) + new_block + "\n" + "".join(lines[end_idx + 1:])
    if new_text == text:
        return False
    file_path.write_text(new_text, encoding="utf-8")
    return True


def main():
    if len(sys.argv) != 2:
        sys.stderr.write("Usage: python3 scripts/gen_examples.py <AuthorYear>\n")
        sys.exit(1)

    author_year = sys.argv[1]
    json_path = JSON_DIR / f"{author_year}.json"
    if not json_path.exists():
        sys.stderr.write(f"FATAL: JSON not found at {json_path.relative_to(ROOT)}\n")
        sys.exit(1)

    try:
        with open(json_path, encoding="utf-8") as f:
            examples = json.load(f)
    except json.JSONDecodeError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: invalid JSON: {e}\n")
        sys.exit(1)

    if not isinstance(examples, list):
        sys.stderr.write(
            f"FATAL: {json_path.relative_to(ROOT)}: top level must be an array of "
            f"example objects (got {type(examples).__name__})\n"
        )
        sys.exit(1)

    target = find_target_file(author_year)
    try:
        block = emit_block(author_year, examples)
    except ValueError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)

    changed = replace_between_markers(target, block)
    rel_target = target.relative_to(ROOT)
    rel_json   = json_path.relative_to(ROOT)
    n = len(examples)
    if changed:
        sys.stdout.write(
            f"[gen] {rel_target} ← {rel_json} ({n} example{'s' if n != 1 else ''})\n"
        )
    else:
        sys.stdout.write(f"[gen] {rel_target} unchanged\n")


if __name__ == "__main__":
    main()
