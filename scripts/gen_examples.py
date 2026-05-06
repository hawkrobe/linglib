#!/usr/bin/env python3
"""Generate Lean 4 LinguisticExample defs from per-paper CSV files.

Usage:
    python3 scripts/gen_examples.py <AuthorYear>

Example:
    python3 scripts/gen_examples.py Charlow2014
        Reads:    Datasets/Examples/Charlow2014.csv
        Locates:  Linglib/Studies/*/Charlow2014.lean (must be unique)
        Inserts:  generated `namespace Examples ... end` block between markers
                  -- ── BEGIN GENERATED EXAMPLES ──
                  -- ── END GENERATED EXAMPLES ──

Behavior:
- Errors out (exit 1) if the CSV doesn't exist.
- Errors out if zero or multiple study files match the AuthorYear.
- Errors out if either marker is missing in the target file.
- Replaces *only* the content between markers; everything else is preserved.
- Idempotent: re-running on unchanged CSV produces no diff.

Defer to follow-on:
- `--check` mode (regenerate in-memory and assert no diff).
- Cross-paper namespace imports (when needed by a 2nd consumer).
- Schema extensions (Tree, multi-LF readings, paradigm clusters, etc.)
- Content-hashed IDs for stable references under correction.

Dependencies: pure stdlib (csv module).
"""

import csv
import sys
from pathlib import Path

ROOT       = Path(__file__).resolve().parent.parent
CSV_DIR    = ROOT / "Datasets" / "Examples"
STUDIES    = ROOT / "Linglib" / "Studies"
PHENOMENA  = ROOT / "Linglib" / "Phenomena"

# Plain ASCII markers — safe across editors / encodings / locales.
BEGIN_MARKER = "-- BEGIN GENERATED EXAMPLES"
END_MARKER   = "-- END GENERATED EXAMPLES"

# CSV columns (CLDF Examples component + two extensions).
EXPECTED_COLS = [
    "ID", "Language_ID", "Primary_Text", "Analyzed_Word", "Gloss",
    "Translated_Text", "Meta_Language_ID", "LGR_Conformance", "Comment",
    "Source_Bibkey", "Source_Label", "Judgment", "Context",
]

# Multi-token fields use "|" as inner separator (avoids comma/tab collision).
MULTI_TOKEN_SEP = "|"

VALID_JUDGMENTS = {
    "acceptable", "marginal", "questionable", "unacceptable", "ungrammatical",
}


def lean_string(s: str) -> str:
    """Quote a string for Lean source. Escapes backslashes and quotes."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_string_list(items: list[str]) -> str:
    """Render a list of strings as a Lean list literal."""
    if not items:
        return "[]"
    return "[" + ", ".join(lean_string(s) for s in items) + "]"


def lean_identifier(example_id: str, author_year_lower: str) -> str:
    """Derive a Lean-valid identifier from a CSV example ID.

    `charlow2014_donkey1` → `donkey1` (strip the AuthorYear_ prefix and use
    the rest as the local identifier inside `namespace Examples`).
    """
    prefix = author_year_lower + "_"
    if example_id.lower().startswith(prefix):
        local = example_id[len(prefix):]
    else:
        local = example_id
    # Replace anything non-identifier with underscore; ensure starts with letter.
    local = "".join(c if c.isalnum() or c == "_" else "_" for c in local)
    if not local or not local[0].isalpha():
        local = "ex_" + local
    return local


def parse_judgment(s: str) -> str:
    s = s.strip().lower()
    if s not in VALID_JUDGMENTS:
        raise ValueError(
            f"invalid Judgment {s!r}; expected one of {sorted(VALID_JUDGMENTS)}"
        )
    return f".{s}"


def lean_pair_list(pairs: list[tuple[str, str]]) -> str:
    """Render a list of string pairs as a Lean list of tuple literals."""
    if not pairs:
        return "[]"
    items = ", ".join(f"({lean_string(a)}, {lean_string(b)})" for a, b in pairs)
    return "[" + items + "]"


def emit_example(row: dict, author_year_lower: str) -> str:
    """Emit one `def <local_id> : LinguisticExample := { ... }` block."""
    ex_id      = row["ID"].strip()
    local_id   = lean_identifier(ex_id, author_year_lower)
    bibkey     = row["Source_Bibkey"].strip()
    label      = row["Source_Label"].strip()
    language   = row["Language_ID"].strip()
    primary    = row["Primary_Text"].strip()
    analyzed   = [t for t in row["Analyzed_Word"].strip().split(MULTI_TOKEN_SEP) if t]
    gloss      = [t for t in row["Gloss"].strip().split(MULTI_TOKEN_SEP) if t]
    if len(analyzed) != len(gloss):
        raise ValueError(
            f"row {ex_id!r}: Analyzed_Word ({len(analyzed)} tokens) and "
            f"Gloss ({len(gloss)} tokens) lengths disagree"
        )
    glossed_pairs = list(zip(analyzed, gloss))
    translation = row["Translated_Text"].strip()
    context    = row["Context"].strip()
    judgment   = parse_judgment(row["Judgment"])
    comment    = row["Comment"].strip()
    meta_lang  = row.get("Meta_Language_ID", "stan1293").strip() or "stan1293"
    lgr        = row.get("LGR_Conformance", "").strip()

    return f"""def {local_id} : LinguisticExample :=
  {{ id := {lean_string(ex_id)}
    source := ⟨{lean_string(bibkey)}, {lean_string(label)}⟩
    language := {lean_string(language)}
    primaryText := {lean_string(primary)}
    glossedTokens := {lean_pair_list(glossed_pairs)}
    translation := {lean_string(translation)}
    context := {lean_string(context)}
    judgment := {judgment}
    comment := {lean_string(comment)}
    metaLanguage := {lean_string(meta_lang)}
    lgrConformance := {lean_string(lgr)} }}"""


def emit_block(author_year: str, rows: list[dict]) -> str:
    """Emit the full `namespace Examples ... end` block for insertion between markers."""
    ay_lower = author_year.lower()
    if not rows:
        body = "-- (no rows in CSV)"
        all_def = "def all : List LinguisticExample := []"
    else:
        body = "\n\n".join(emit_example(r, ay_lower) for r in rows)
        local_ids = [lean_identifier(r["ID"].strip(), ay_lower) for r in rows]
        all_def = f"def all : List LinguisticExample := [{', '.join(local_ids)}]"

    return f"""{BEGIN_MARKER}
-- (Generated from Datasets/Examples/{author_year}.csv by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the CSV.)

namespace Examples
open Datasets.Examples

{body}

{all_def}

end Examples
{END_MARKER}"""


def find_target_file(author_year: str) -> Path:
    """Locate the unique study file matching <AuthorYear>.lean.

    Searches both the new top-level layout (`Linglib/Studies/*/`) and the
    legacy layout (`Linglib/Phenomena/*/Studies/`) so the generator works
    on all phenomena during the in-progress relocation. Errors on 0 or >1
    matches across both locations.
    """
    new_matches    = list(STUDIES.glob(f"*/{author_year}.lean"))
    legacy_matches = list(PHENOMENA.glob(f"*/Studies/{author_year}.lean"))
    matches        = new_matches + legacy_matches

    if len(matches) == 0:
        sys.stderr.write(
            f"FATAL: no study file found for {author_year}; checked:\n"
            f"  Linglib/Studies/*/{author_year}.lean\n"
            f"  Linglib/Phenomena/*/Studies/{author_year}.lean\n"
            f"Create the file (with marker block) before running the generator.\n"
        )
        sys.exit(1)
    if len(matches) > 1:
        paths = "\n  ".join(str(p.relative_to(ROOT)) for p in matches)
        sys.stderr.write(
            f"FATAL: ambiguous match for {author_year}; found multiple study files:\n"
            f"  {paths}\n"
        )
        sys.exit(1)
    return matches[0]


def replace_between_markers(file_path: Path, new_block: str) -> bool:
    """Replace content between BEGIN/END markers. Return True if file changed."""
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
    csv_path = CSV_DIR / f"{author_year}.csv"
    if not csv_path.exists():
        sys.stderr.write(f"FATAL: CSV not found at {csv_path.relative_to(ROOT)}\n")
        sys.exit(1)

    with open(csv_path, encoding="utf-8") as f:
        reader = csv.DictReader(f)
        missing = set(EXPECTED_COLS) - set(reader.fieldnames or [])
        if missing:
            sys.stderr.write(
                f"FATAL: CSV {csv_path.relative_to(ROOT)} missing columns: {sorted(missing)}\n"
            )
            sys.exit(1)
        rows = list(reader)

    target = find_target_file(author_year)
    block = emit_block(author_year, rows)
    changed = replace_between_markers(target, block)

    rel_target = target.relative_to(ROOT)
    rel_csv    = csv_path.relative_to(ROOT)
    if changed:
        sys.stdout.write(
            f"[gen] {rel_target} ← {rel_csv} ({len(rows)} example{'s' if len(rows) != 1 else ''})\n"
        )
    else:
        sys.stdout.write(f"[gen] {rel_target} unchanged\n")


if __name__ == "__main__":
    main()
