#!/usr/bin/env python3
"""Ratchet for the gradual migration to the Lean module system.

A module may import only modules, while a non-module may import anything, so
the migration walks downstream from the leaves. A file is on the *frontier*
when it is not yet a module and every file it imports already is one: it can
be converted today without touching anything else.

Usage:
    python3 scripts/check_module_frontier.py
        List the frontier and print migration counts. Always exits 0.
    python3 scripts/check_module_frontier.py --staged
        Pre-commit mode. Exits 1 if a newly added staged file is on the
        frontier; warns about modified ones.
    python3 scripts/check_module_frontier.py --fix FILE [FILE ...]
        Convert frontier files in place: `module` after the copyright header,
        `import` -> `public import`, and `@[expose] public section` after the
        module docstring. Build the file and its importers afterwards; files
        with only theorems can use a plain `public section`.

Install as a pre-commit hook:
    cp scripts/git-hooks/pre-commit "$(git rev-parse --git-common-dir)/hooks/"

Dependencies: pure stdlib + `git`.
"""

from __future__ import annotations

import re
import subprocess
import sys
from functools import lru_cache
from pathlib import Path

IMPORT_RE = re.compile(
    r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)\s*$')
PLAIN_IMPORT_RE = re.compile(r'^import\s+')


def repo_root() -> Path:
    out = subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True)
    return Path(out.strip())


ROOT = repo_root()


def git_lines(*args: str) -> list[str]:
    out = subprocess.check_output(['git', *args], text=True, cwd=ROOT)
    return [line for line in out.splitlines() if line]


def header_of(lines) -> tuple[bool, list[str]]:
    """Whether the lines of a Lean file declare a module, and the modules they import."""
    is_module, imports, in_comment = False, [], False
    for line in lines:
        stripped = line.strip()
        if in_comment:
            in_comment = '-/' not in stripped
            continue
        if stripped.startswith('/-'):
            if imports or is_module:
                break  # the module docstring ends the import block
            in_comment = '-/' not in stripped
            continue
        if not stripped or stripped.startswith('--'):
            continue
        if stripped.split('--')[0].strip() == 'module':
            is_module = True
            continue
        m = IMPORT_RE.match(line)
        if not m:
            break
        imports.append(m.group(1))
    return is_module, imports


def header(path: Path) -> tuple[bool, list[str]]:
    """Whether the file is a module, and the modules it imports."""
    with open(path, encoding='utf-8') as f:
        return header_of(f)


def module_path(name: str) -> Path | None:
    rel = Path(*name.split('.')).with_suffix('.lean')
    if name.startswith('Linglib.'):
        return ROOT / rel
    for pkg in (ROOT / '.lake' / 'packages').glob('*'):
        if (pkg / rel).exists():
            return pkg / rel
    return None


@lru_cache(maxsize=None)
def import_is_module(name: str) -> bool:
    path = module_path(name)
    if path is None or not path.exists():
        # Core `Lean`/`Std`/`Init` and packages not checked out: all modules.
        return not name.startswith('Linglib.')
    return header(path)[0]


def on_frontier(rel: str) -> bool:
    is_module, imports = header(ROOT / rel)
    return not is_module and all(import_is_module(i) for i in imports)


def tracked() -> list[str]:
    return git_lines('ls-files', 'Linglib/*.lean')


def report() -> int:
    files = tracked()
    modules = sum(header(ROOT / f)[0] for f in files)
    frontier = [f for f in files if on_frontier(f)]
    for f in frontier:
        print(f)
    print(f'{modules} of {len(files)} files are modules; {len(frontier)} on the frontier',
          file=sys.stderr)
    return 0


def staged() -> int:
    blocked = []
    for status, flag in (('A', True), ('M', False)):
        for f in git_lines('diff', '--cached', '--name-only', f'--diff-filter={status}',
                           '--', 'Linglib/*.lean'):
            if not on_frontier(f):
                continue
            if flag:
                blocked.append(f)
            else:
                print(f'note: {f} imports only modules and could become one', file=sys.stderr)
    if blocked:
        print('New files that import only modules must be modules themselves:', file=sys.stderr)
        for f in blocked:
            print(f'  {f}', file=sys.stderr)
        print('Convert with: python3 scripts/check_module_frontier.py --fix <file>, then build.',
              file=sys.stderr)
        return 1
    return 0


def header_import_lines(lines: list[str]) -> list[int]:
    """The indices of the import lines at the head of a file, before any other code or the
    module docstring; `import` at the start of a line further down is not one."""
    found, in_comment = [], False
    for i, line in enumerate(lines):
        stripped = line.strip()
        if in_comment:
            in_comment = '-/' not in stripped
            continue
        if stripped.startswith('/-'):
            if found or stripped.startswith('/-!'):
                break
            in_comment = '-/' not in stripped
            continue
        if not stripped or stripped.startswith('--') or stripped.split('--')[0].strip() == 'module':
            continue
        if not PLAIN_IMPORT_RE.match(line):
            break
        found.append(i)
    return found


def modularize(text: str) -> str:
    """The text of a Lean file as a module: `module` after the copyright comment, every
    `import` a `public import`, and `@[expose] public section` after the module docstring."""
    lines = text.split('\n')
    import_lines = header_import_lines(lines)
    if import_lines:
        first, last = import_lines[0], import_lines[-1]
        after = last + 1
    else:
        # No imports: `module` goes after the copyright comment, if there is one.
        first = 0
        if lines and lines[0].startswith('/-') and not lines[0].startswith('/-!'):
            first = next(i for i, l in enumerate(lines) if '-/' in l) + 1
            while first < len(lines) and not lines[first].strip():
                first += 1
        after = first
    # End of the module docstring, if one follows the imports.
    section_at = after
    doc = next((i for i in range(after, len(lines)) if lines[i].strip()), None)
    if doc is not None and lines[doc].startswith('/-!'):
        section_at = next(i for i in range(doc, len(lines)) if '-/' in lines[i]) + 1
    lines[section_at:section_at] = ['', '@[expose] public section']
    for i in import_lines:
        lines[i] = PLAIN_IMPORT_RE.sub('public import ', lines[i])
    lines[first:first] = ['module', '']
    return '\n'.join(lines)


def as_module_if_possible(text: str) -> str:
    """Generated Lean text as a module when everything it imports is one, else unchanged."""
    is_module, imports = header_of(text.split('\n'))
    if is_module or not all(import_is_module(i) for i in imports):
        return text
    return modularize(text)


def import_stmt(host_text: str, module: str) -> str:
    """The line importing `module` into a file with text `host_text`: public in a module."""
    return f"{'public ' if header_of(host_text.split(chr(10)))[0] else ''}import {module}"


def fix(paths: list[str]) -> int:
    status = 0
    for p in paths:
        rel = str(Path(p).resolve().relative_to(ROOT))
        if not on_frontier(rel):
            print(f'skipped {rel}: already a module, or it imports a non-module', file=sys.stderr)
            status = 1
            continue
        path = ROOT / rel
        path.write_text(modularize(path.read_text(encoding='utf-8')), encoding='utf-8')
        print(f'converted {rel}')
    return status


def main() -> int:
    args = sys.argv[1:]
    if args[:1] == ['--staged']:
        return staged()
    if args[:1] == ['--fix']:
        return fix(args[1:])
    return report()


if __name__ == '__main__':
    sys.exit(main())
