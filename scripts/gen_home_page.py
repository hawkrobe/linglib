#!/usr/bin/env python3
"""Generate the landing page published at linglib.io/.

The page links the API documentation, the scoreboard, the bibliography and the repository.

Usage, from the repository root:

    python3 scripts/gen_home_page.py            # write .lake/build/doc-site/index.html
    python3 scripts/gen_home_page.py --out DIR  # write DIR/index.html
"""

import argparse
import datetime
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = ROOT / "scripts" / "home_page" / "template.html"
PAPERMOD_CSS = ROOT / "scripts" / "papermod.css"
DEFAULT_OUT = ROOT / ".lake" / "build" / "doc-site"
REPO = "https://github.com/linglib-community/linglib"


def git_commit():
    sha = os.environ.get("GITHUB_SHA")
    if not sha:
        try:
            sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                                 text=True, check=True).stdout.strip()
        except (OSError, subprocess.CalledProcessError):
            sha = ""
    return sha


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT, help="directory for index.html")
    args = ap.parse_args()

    sha = git_commit()
    page = (TEMPLATE.read_text(encoding="utf-8")
            .replace("/*PAPERMOD_CSS*/", PAPERMOD_CSS.read_text(encoding="utf-8"))
            .replace("__BUILT__", datetime.date.today().isoformat())
            .replace("__COMMIT_SHORT__", sha[:9])
            .replace("__COMMIT_HREF__", f"{REPO}/tree/{sha}" if sha else REPO))
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "index.html").write_text(page, encoding="utf-8")
    print(f"wrote {args.out / 'index.html'}")


if __name__ == "__main__":
    main()
