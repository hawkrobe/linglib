#!/usr/bin/env python3
"""Generate Lean 4 LinguisticExample modules from per-paper JSON files.

Usage:
    python3 scripts/gen_examples.py <AuthorYear>
    python3 scripts/gen_examples.py --all                # regenerate every paper
    python3 scripts/gen_examples.py --check [<AuthorYear>]  # verify sync, no writes

Example:
    python3 scripts/gen_examples.py Charlow2014
        Reads:   Linglib/Data/Examples/Charlow2014.json
        Writes:  Linglib/Data/Examples/Charlow2014.lean — a standalone
                 auto-generated module declaring `namespace
                 Charlow2014.Examples`. Consumers (the paper's study file,
                 test-suite hubs) `import Linglib.Data.Examples.Charlow2014`.

Legacy migration: earlier versions spliced a generated block between
`-- BEGIN GENERATED EXAMPLES` / `-- END GENERATED EXAMPLES` markers inside
the study file (routed by an optional `<AuthorYear>.target` sidecar). When a
host file still carries such a block, this script removes it, inserts the
module import into that file, and deletes any retired `.target` sidecar.
The `Linglib.lean` root import is kept in sync automatically (appended,
per the repo's append-ordered convention).

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
- Errors out on schema violations (unknown judgment value, gloss/word
  length mismatch, missing required field, missing source.bibkey).
- Idempotent: re-running on unchanged JSON produces no diff.
- `--check` regenerates in-memory and exits 1 on any drift (CI guard);
  writes nothing.

Defer to follow-on:
- Schema extensions (Tree, indexed anaphora, paper-relativized
  classifications) when a consuming study demands them.

Dependencies: pure stdlib (json module).
"""

import json
import re
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


def emit_module(author_year: str, examples: list) -> str:
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

    return f"""import Linglib.Data.Examples.Schema

/-!
# `{author_year}` — typed example data

Auto-generated from `Linglib/Data/Examples/{author_year}.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace {author_year}.Examples`.
-/

namespace {author_year}.Examples

open Data.Examples

{body}

{all_def}

end {author_year}.Examples
"""


def find_legacy_hosts(author_year: str) -> list[Path]:
    """Files that may still carry a legacy marker block for this paper:
    the `.target` sidecar's host (if any), the flat study file, and any
    file in a multi-file paper subdir. Only files actually containing
    both markers are returned (empty list for already-migrated papers)."""
    candidates: list[Path] = []
    sidecar = JSON_DIR / f"{author_year}.target"
    if sidecar.exists():
        for raw in sidecar.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if line and not line.startswith("#"):
                resolved = (ROOT / line).resolve()
                if resolved.exists():
                    candidates.append(resolved)
                break
    flat = STUDIES / f"{author_year}.lean"
    if flat.exists():
        candidates.append(flat)
    subdir = STUDIES / author_year
    if subdir.is_dir():
        candidates.extend(sorted(subdir.glob("*.lean")))
    hosts = []
    for path in candidates:
        body = path.read_text(encoding="utf-8")
        if BEGIN_MARKER in body and END_MARKER in body and path not in hosts:
            hosts.append(path)
    return hosts


def remove_marker_block(file_path: Path) -> None:
    """Delete the legacy generated block, markers included, collapsing
    the surrounding blank lines to a single separator."""
    body = file_path.read_text(encoding="utf-8")
    lines = body.splitlines(keepends=True)
    begin_idx = end_idx = None
    for i, line in enumerate(lines):
        if line.rstrip("\n") == BEGIN_MARKER and begin_idx is None:
            begin_idx = i
        elif line.rstrip("\n") == END_MARKER and end_idx is None:
            end_idx = i
    if begin_idx is None or end_idx is None or end_idx <= begin_idx:
        return
    before = "".join(lines[:begin_idx]).rstrip("\n")
    after = "".join(lines[end_idx + 1:]).lstrip("\n")
    if before and after:
        new_body = before + "\n\n" + after
    else:
        new_body = before + after
    if not new_body.endswith("\n"):
        new_body += "\n"
    file_path.write_text(new_body, encoding="utf-8")


def ensure_import(file_path: Path, module: str) -> bool:
    """Insert `import <module>` after the file's last import line if
    absent. Returns True if the file changed."""
    body = file_path.read_text(encoding="utf-8")
    stmt = f"import {module}"
    if re.search(rf"^{re.escape(stmt)}\s*$", body, flags=re.M):
        return False
    lines = body.splitlines(keepends=True)
    last_import = None
    for i, line in enumerate(lines):
        if line.startswith("import "):
            last_import = i
    if last_import is None:
        lines.insert(0, stmt + "\n")
    else:
        lines.insert(last_import + 1, stmt + "\n")
    file_path.write_text("".join(lines), encoding="utf-8")
    return True


def process(author_year: str, check: bool) -> bool:
    """Generate (or, with `check`, verify) one paper's module.

    Returns True on success / in-sync; False on drift in check mode.
    Exits on malformed input (both modes)."""
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

    try:
        module_text = emit_module(author_year, examples)
    except ValueError as e:
        sys.stderr.write(f"FATAL: {json_path.relative_to(ROOT)}: {e}\n")
        sys.exit(1)

    module_path = JSON_DIR / f"{author_year}.lean"
    module_name = f"Linglib.Data.Examples.{author_year}"
    rel_module = module_path.relative_to(ROOT)
    rel_json = json_path.relative_to(ROOT)
    n = len(examples)

    in_sync = (
        module_path.exists()
        and module_path.read_text(encoding="utf-8") == module_text
    )

    if check:
        if in_sync:
            sys.stdout.write(f"[check] {rel_module} in sync\n")
        else:
            sys.stderr.write(
                f"[check] DRIFT: {rel_module} does not match {rel_json}; "
                f"run scripts/gen_examples.py {author_year}\n"
            )
        return in_sync

    if in_sync:
        sys.stdout.write(f"[gen] {rel_module} unchanged\n")
    else:
        module_path.write_text(module_text, encoding="utf-8")
        sys.stdout.write(
            f"[gen] {rel_module} \u2190 {rel_json} ({n} example{'s' if n != 1 else ''})\n"
        )

    # Legacy migration: strip old marker blocks, wire the module import.
    for host in find_legacy_hosts(author_year):
        remove_marker_block(host)
        ensure_import(host, module_name)
        sys.stdout.write(
            f"[gen] migrated legacy block out of {host.relative_to(ROOT)}\n"
        )
    sidecar = JSON_DIR / f"{author_year}.target"
    if sidecar.exists():
        sidecar.unlink()
        sys.stdout.write(
            f"[gen] removed retired sidecar {sidecar.relative_to(ROOT)}\n"
        )

    if ensure_import(ROOT / "Linglib.lean", module_name):
        sys.stdout.write(f"[gen] added {module_name} import to Linglib.lean\n")
    return True


# Canonical JSON formatting: 2-space indent, schema key order, and compact
# leaf collections (gloss pairs packed onto wrapped lines; one feature pair /
# alternative / reading per line) so a python round-trip never explodes them.

KEY_ORDER = [
    "id", "source", "reportedIn", "language", "primaryText",
    "discourseSegments", "glossedTokens", "translation", "context",
    "judgment", "alternatives", "readings", "paperFeatures", "comment",
    "metaLanguage", "lgrConformance",
]

MAX_WIDTH = 98


def _j(v) -> str:
    return json.dumps(v, ensure_ascii=False)


def _fmt_inline_list(items: list[str], indent: str) -> str:
    """Render pre-serialized items inside [...], packing them onto lines of
    at most MAX_WIDTH characters."""
    if not items:
        return "[]"
    lines, cur = [], ""
    for it in items:
        cand = it if not cur else f"{cur}, {it}"
        if cur and len(indent) + 2 + len(cand) > MAX_WIDTH:
            lines.append(cur + ",")
            cur = it
        else:
            cur = cand
    lines.append(cur)
    body = "\n".join(f"{indent}  {l}" for l in lines)
    return f"[\n{body}\n{indent}]"


def _fmt_per_line_list(items: list[str], indent: str) -> str:
    """Render pre-serialized items inside [...], one per line."""
    if not items:
        return "[]"
    body = ",\n".join(f"{indent}  {it}" for it in items)
    return f"[\n{body}\n{indent}]"


def _fmt_obj_inline(o: dict) -> str:
    return "{" + ", ".join(f"{_j(k)}: {_j(v)}" for k, v in o.items()) + "}"


def _fmt_value(key: str, v, indent: str) -> str:
    if v is None or isinstance(v, (str, int, float, bool)):
        return _j(v)
    if isinstance(v, dict):
        return _fmt_obj_inline(v)
    if isinstance(v, list):
        if key == "glossedTokens":
            return _fmt_inline_list([_j(x) for x in v], indent)
        if key in ("paperFeatures", "alternatives", "readings"):
            items = [
                _fmt_obj_inline(x) if isinstance(x, dict) else _j(x) for x in v
            ]
            return _fmt_per_line_list(items, indent)
        if key == "discourseSegments":
            return _fmt_per_line_list([_j(x) for x in v], indent)
        return _j(v)
    return _j(v)


def format_examples(examples: list) -> str:
    """Canonical text for a per-paper JSON file."""
    out = ["["]
    for i, ex in enumerate(examples):
        out.append("  {")
        keys = [k for k in KEY_ORDER if k in ex]
        keys += [k for k in ex if k not in KEY_ORDER]  # never drop unknown keys
        for j, k in enumerate(keys):
            comma = "," if j < len(keys) - 1 else ""
            out.append(f"    {_j(k)}: {_fmt_value(k, ex[k], '    ')}{comma}")
        out.append("  }," if i < len(examples) - 1 else "  }")
    out.append("]")
    return "\n".join(out) + "\n"


def fmt(author_year: str) -> bool:
    """Rewrite a JSON file in canonical format. Refuses to write (and
    returns False) if the formatted text does not parse back to the
    identical data."""
    json_path = JSON_DIR / f"{author_year}.json"
    with open(json_path, encoding="utf-8") as f:
        examples = json.load(f)
    text = format_examples(examples)
    if json.loads(text) != examples:
        sys.stderr.write(
            f"[fmt] REFUSING {json_path.relative_to(ROOT)}: round-trip mismatch\n"
        )
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
            "Usage: python3 scripts/gen_examples.py <AuthorYear> | --all\n"
            "       python3 scripts/gen_examples.py --check [<AuthorYear>]\n"
            "       python3 scripts/gen_examples.py --fmt [<AuthorYear>]\n"
            "  --all    regenerate every Linglib/Data/Examples/*.json\n"
            "  --check  verify generated modules match JSON (no writes); "
            "exit 1 on drift\n"
            "  --fmt    rewrite JSON in canonical format (data-preserving)\n"
        )
        sys.exit(1)

    if do_fmt:
        if not all([fmt(p) for p in papers]):
            sys.exit(1)
        return

    ok = all([process(p, check) for p in papers])
    if not ok:
        sys.exit(1)


if __name__ == "__main__":
    main()
