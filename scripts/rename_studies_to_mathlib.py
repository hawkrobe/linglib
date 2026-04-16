#!/usr/bin/env python3
"""Rename Phenomena/<X>/Studies/...AuthorYear.lean namespaces to mathlib style.

For a given phenomenon directory (or all if --all), walks every
`Phenomena/<X>/Studies/.../AuthorYear.lean` whose primary namespace is
`Phenomena.<X>.Studies.<...>.<AuthorYear>` and renames it to bare
`<AuthorYear>`.

Then sweeps the entire repo, replacing references in three forms:
  - `Phenomena.<X>.Studies.<...>.<AuthorYear>` → `<AuthorYear>`
  - `_root_.Phenomena.<X>.Studies.<...>.<AuthorYear>` → `_root_.<AuthorYear>`
  - `Studies.<AuthorYear>` → `<AuthorYear>`
    (the partial form that resolved via parent-namespace lookup before)

The third pattern is restricted to `<AuthorYear>` values that match a
study we just renamed, so it won't replace unrelated `Studies.X` strings.

Skips `import` lines (file paths don't change just because namespaces do)
and preserves CRLF line endings.

Usage:
    python3 scripts/rename_studies_to_mathlib.py --phenomenon Politeness
    python3 scripts/rename_studies_to_mathlib.py --phenomenon Politeness --dry-run
    python3 scripts/rename_studies_to_mathlib.py --all
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LINGLIB_DIR = REPO_ROOT / "Linglib"


def expected_path_namespace(study_file: Path) -> str | None:
    """`Phenomena.X.Studies.Y` from `Linglib/Phenomena/X/Studies/Y.lean`."""
    parts = study_file.relative_to(REPO_ROOT).parts
    if parts[0] != "Linglib" or parts[1] != "Phenomena":
        return None
    if "Studies" not in parts:
        return None
    components = list(parts[1:])
    components[-1] = components[-1].removesuffix(".lean")
    return ".".join(components)


def file_primary_namespace(study_file: Path) -> str | None:
    """First top-level `namespace X` declaration."""
    in_block = 0
    stack: list[str] = []
    for line in study_file.read_text(encoding="utf-8").splitlines():
        # Crude block-comment skip
        s = line
        i = 0
        while i < len(s):
            if in_block > 0:
                if s[i:i+2] == "-/":
                    in_block -= 1
                    i += 2
                elif s[i:i+2] == "/-":
                    in_block += 1
                    i += 2
                else:
                    i += 1
            else:
                if s[i:i+2] == "/-":
                    in_block += 1
                    i += 2
                elif s[i:i+2] == "--":
                    break
                else:
                    i += 1
        if in_block > 0:
            continue
        stripped = line.strip()
        m = re.match(r"^namespace\s+(\S+)", stripped)
        if m and not stack:
            return m.group(1)
        if m:
            stack.append("ns")
        elif re.match(r"^section\b", stripped):
            stack.append("sec")
        elif re.match(r"^end\b", stripped) and stack:
            stack.pop()
    return None


def collect_studies(phenomenon: str | None) -> list[tuple[Path, str, str]]:
    """Return (file, old_namespace, new_namespace) for renamable studies.

    Only returns studies whose primary namespace IS the path-mirror
    `Phenomena.<X>.Studies.<...>.<AuthorYear>` — concept-named studies
    (e.g. `Minimalism.Phenomena.Allocutivity`) are skipped.
    """
    out = []
    pattern = "Phenomena/*/Studies/**/*.lean" if phenomenon is None \
        else f"Phenomena/{phenomenon}/Studies/**/*.lean"
    for f in sorted(LINGLIB_DIR.rglob(pattern)):
        expected = expected_path_namespace(f)
        if expected is None:
            continue
        primary = file_primary_namespace(f)
        if primary != expected:
            continue
        new = f.stem
        out.append((f, expected, new))
    return out


def apply_renames(studies: list[tuple[Path, str, str]],
                  dry_run: bool) -> tuple[int, int]:
    """Apply all rename rules across the entire library."""
    if not studies:
        return (0, 0)

    rename_map = {old: new for _, old, new in studies}
    new_names = {new for _, _, new in studies}

    # Pattern 1: full path Phenomena.X.Studies....AuthorYear (longest first).
    sorted_olds = sorted(rename_map, key=len, reverse=True)
    full_pattern = re.compile(
        r"(?<![A-Za-z0-9_])"  # no leading word char (allow leading `.`)
        r"(?:" + "|".join(re.escape(o) for o in sorted_olds) + r")"
        r"(?![A-Za-z0-9_])"
    )

    # Pattern 2: partial `Studies.AuthorYear` for our renamed names only.
    sorted_news = sorted(new_names, key=len, reverse=True)
    partial_pattern = re.compile(
        r"(?<![A-Za-z0-9_.])"  # require non-`.` boundary so we don't
                                # match `Foo.Studies.Y` (which is wrong
                                # to rewrite — only `Studies.Y` standalone)
        r"Studies\.(?:" + "|".join(re.escape(n) for n in sorted_news) + r")"
        r"(?![A-Za-z0-9_])"
    )

    def replace_full(m: re.Match) -> str:
        return rename_map[m.group(0)]

    def replace_partial(m: re.Match) -> str:
        # Strip the leading 'Studies.'
        return m.group(0)[len("Studies."):]

    grand_total = 0
    files_touched: set[Path] = set()
    for f in sorted(LINGLIB_DIR.rglob("*.lean")):
        raw = f.read_bytes()
        text = raw.decode("utf-8")
        new_lines = []
        file_total = 0
        for line in text.splitlines(keepends=True):
            if re.match(r"^\s*import\s+", line):
                new_lines.append(line)
                continue
            new_line, n1 = full_pattern.subn(replace_full, line)
            new_line, n2 = partial_pattern.subn(replace_partial, new_line)
            new_lines.append(new_line)
            file_total += n1 + n2
        if file_total > 0:
            files_touched.add(f)
            grand_total += file_total
            if not dry_run:
                f.write_bytes("".join(new_lines).encode("utf-8"))

    return (grand_total, len(files_touched))


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--phenomenon", help="single phenomenon dir name "
                        "(e.g. 'Politeness'). Mutually exclusive with --all.")
    parser.add_argument("--all", action="store_true",
                        help="rename studies across ALL phenomena")
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing")
    args = parser.parse_args()

    if not args.phenomenon and not args.all:
        parser.error("must specify --phenomenon NAME or --all")
    if args.phenomenon and args.all:
        parser.error("--phenomenon and --all are mutually exclusive")

    studies = collect_studies(args.phenomenon)
    print(f"Found {len(studies)} study file(s) to rename")
    if studies and len(studies) <= 30:
        for f, old, new in studies:
            rel = f.relative_to(REPO_ROOT).as_posix()
            print(f"  {rel}: {old} -> {new}")

    total, n_files = apply_renames(studies, args.dry_run)
    verb = "would change" if args.dry_run else "changed"
    print(f"\n{verb} {total} occurrence(s) across {n_files} file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
