#!/usr/bin/env python3
"""Atomically prepend an entry to CHANGELOG.md's `## [Unreleased]` section.

CHANGELOG.md is ~34k lines and concurrent Claude sessions racing to
modify it have lost ~3 entries (0.230.575, 0.230.578, 0.230.586) to
read-then-edit collisions. This script narrows the race window to a
single open+truncate+rename cycle guarded by `flock`, and leaves the
file in a consistent state at every instant.

Usage:
    python3 scripts/changelog_add.py < entry.md
    cat entry.md | python3 scripts/changelog_add.py
    python3 scripts/changelog_add.py <<EOF
    ### 0.230.587 — short title

    Body paragraph.

    - bullet 1
    - bullet 2
    EOF

The entry on stdin must:
- Begin with `### ` (markdown H3 heading; the version line)
- End with whatever you want the entry to contain (trailing newline added)
- NOT include the `## [Unreleased]` marker (the script preserves it)

Convention (per CLAUDE.md "Git Conventions"): all CHANGELOG modifications
should go through this script rather than direct `Edit` calls. Direct
edits work but expose a multi-second race window; the script reduces it
to milliseconds and adds an `flock` guard for cooperative sessions.
"""
from __future__ import annotations

import fcntl
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CHANGELOG = REPO_ROOT / "CHANGELOG.md"
LOCKFILE = REPO_ROOT / ".CHANGELOG.md.lock"
MARKER = "## [Unreleased]"


def main() -> int:
    entry = sys.stdin.read().rstrip()
    if not entry:
        print("error: no entry provided on stdin", file=sys.stderr)
        return 1
    if not entry.startswith("### "):
        print(
            "error: entry must begin with '### ' (markdown H3 heading)",
            file=sys.stderr,
        )
        return 1
    # Reject only if the marker appears as a standalone heading line —
    # a prose mention (e.g., quoted in body text) is fine.
    marker_as_heading = "\n" + MARKER + "\n"
    if entry.startswith(MARKER + "\n") or marker_as_heading in entry:
        print(
            f"error: entry must NOT include the '{MARKER}' marker "
            "as a heading line (the script preserves it)",
            file=sys.stderr,
        )
        return 1

    # Acquire exclusive lock for the duration of read+write+rename.
    # Cooperative: only blocks against other invocations of THIS script.
    # Direct Edit calls will not honor the lock.
    with open(LOCKFILE, "w") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)

        content = CHANGELOG.read_text(encoding="utf-8")

        marker_line = MARKER + "\n"
        idx = content.find(marker_line)
        if idx < 0:
            print(
                f"error: '{MARKER}' line not found in {CHANGELOG}",
                file=sys.stderr,
            )
            return 1

        # Insert position: right after the marker line + the blank line
        # that conventionally follows it.
        insert_at = idx + len(marker_line)
        if insert_at < len(content) and content[insert_at] == "\n":
            insert_at += 1

        new_content = (
            content[:insert_at]
            + entry
            + "\n\n"
            + content[insert_at:]
        )

        # Atomic write: tmpfile in the same directory + rename.
        # Same-filesystem rename is atomic on POSIX.
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            delete=False,
            dir=CHANGELOG.parent,
            prefix=".CHANGELOG.tmp.",
        ) as tmp:
            tmp.write(new_content)
            tmp_path = Path(tmp.name)

        tmp_path.replace(CHANGELOG)

    return 0


if __name__ == "__main__":
    sys.exit(main())
