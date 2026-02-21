#!/usr/bin/env python3
"""Generate blog/content/bibliography.md from blog/data/references.bib.

Also scans Lean source files for @cite{key} references, validates them
against the .bib, and appends a "cited in" reverse index to each entry.

Usage:
    python blog/scripts/gen_bibliography.py          # generate bibliography.md
    python blog/scripts/gen_bibliography.py --check   # validate only (no output)
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

REPO = "https://github.com/hawkrobe/linglib/blob/main/Linglib"
ROOT = Path(__file__).resolve().parent.parent
PROJECT_ROOT = ROOT.parent
LEAN_DIR = PROJECT_ROOT / "Linglib"
BIB_PATH = ROOT / "data" / "references.bib"
OUT_PATH = ROOT / "content" / "bibliography.md"

SUBFIELD_LABELS = {
    "pragmatics/rsa": "Pragmatics — Rational Speech Acts",
    "pragmatics/neogricean": "Pragmatics — NeoGricean / Exhaustivity",
    "pragmatics/dts": "Pragmatics — Decision-Theoretic Semantics",
    "semantics/compositional": "Semantics — Compositional / Montague",
    "semantics/modality": "Semantics — Modality & Conditionals",
    "semantics/conditionals": "Semantics — Modality & Conditionals",
    "semantics/reference": "Semantics — Reference & Attitudes",
    "semantics/focus": "Semantics — Focus & Information Structure",
    "semantics/causation": "Semantics — Causation",
    "semantics/tense": "Semantics — Tense & Aspect",
    "semantics/lexical": "Semantics — Lexical (Adjectives, Nouns, Plurals, Events)",
    "semantics/questions": "Semantics — Questions",
    "semantics/presupposition": "Semantics — Presupposition & Entailment",
    "semantics/dynamic": "Semantics — Dynamic Semantics",
    "syntax": "Syntax",
    "comparative": "Cross-Framework Comparisons",
}

SUBFIELD_ORDER = list(SUBFIELD_LABELS.keys())

ROLE_BADGE = {
    "formalized": "formalized",
    "cited": "cited",
    "foundational": "foundational",
}

CITE_RE = re.compile(r"@cite\{([^}]+)\}")


# ---------------------------------------------------------------------------
# Minimal BibTeX parser — handles the controlled format used in references.bib
# ---------------------------------------------------------------------------

def clean_bibtex_value(val: str) -> str:
    """Strip BibTeX braces and resolve common LaTeX accents."""
    val = val.strip()
    if val.startswith("{") and val.endswith("}"):
        val = val[1:-1]
    replacements = {
        '{\\"u}': "ü", '{\\"o}': "ö", '{\\"a}': "ä",
        "{\\'e}": "é", "{\\'E}": "É",
        "{\\v{z}}": "ž", "{\\v{c}}": "č", "{\\v{s}}": "š",
        "{\\c{c}}": "ç",
        "{\\ss}": "ß",
    }
    for latex, char in replacements.items():
        val = val.replace(latex, char)
    val = re.sub(r"\{([^{}]*)\}", r"\1", val)
    val = val.replace("``", "\u201c").replace("''", "\u201d")
    return val


def parse_bib(path: Path) -> list[dict]:
    """Parse a .bib file into a list of entry dicts."""
    text = path.read_text(encoding="utf-8")
    entries = []
    for m in re.finditer(
        r"@(\w+)\s*\{([^,]+),\s*(.*?)\n\}", text, re.DOTALL
    ):
        entry_type = m.group(1).lower()
        key = m.group(2).strip()
        body = m.group(3)
        fields = {"_type": entry_type, "_key": key}
        for fm in re.finditer(
            r"(\w[\w-]*)\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}", body
        ):
            fname = fm.group(1).lower()
            fval = clean_bibtex_value(fm.group(2))
            fields[fname] = fval
        entries.append(fields)
    return entries


# ---------------------------------------------------------------------------
# @cite{key} scanner
# ---------------------------------------------------------------------------

def scan_citations(lean_dir: Path) -> dict[str, list[str]]:
    """Scan all .lean files for @cite{key}. Returns {key: [relative_paths]}."""
    cited_by: dict[str, list[str]] = defaultdict(list)
    for lean_file in lean_dir.rglob("*.lean"):
        try:
            text = lean_file.read_text(encoding="utf-8")
        except (UnicodeDecodeError, PermissionError):
            continue
        for m in CITE_RE.finditer(text):
            cite_key = m.group(1).strip()
            rel = str(lean_file.relative_to(lean_dir.parent))
            if rel not in cited_by[cite_key]:
                cited_by[cite_key].append(rel)
    return dict(cited_by)


def validate_citations(
    bib_keys: set[str], cited_by: dict[str, list[str]]
) -> list[str]:
    """Return warning messages for @cite keys not found in .bib."""
    warnings = []
    for key, files in sorted(cited_by.items()):
        if key not in bib_keys:
            for f in files:
                warnings.append(f"WARNING: @cite{{{key}}} in {f} not found in references.bib")
    return warnings


# ---------------------------------------------------------------------------
# Formatting
# ---------------------------------------------------------------------------

def format_authors(raw: str) -> str:
    """Convert 'Last, First and Last, First' to 'Last, F. & Last, F.'"""
    parts = [a.strip() for a in raw.split(" and ")]
    formatted = []
    for part in parts:
        if ", " in part:
            last, firsts = part.split(", ", 1)
            initials = " ".join(
                f"{w[0]}." for w in firsts.split() if w
            )
            formatted.append(f"{last}, {initials}")
        else:
            formatted.append(part)
    if len(formatted) <= 2:
        return " & ".join(formatted)
    return ", ".join(formatted[:-1]) + " & " + formatted[-1]


def format_venue(entry: dict) -> str:
    """Build a venue string from BibTeX fields."""
    etype = entry["_type"]
    parts = []

    if etype == "article":
        if "journal" in entry:
            j = entry["journal"]
            if "volume" in entry:
                j += f", {entry['volume']}"
                if "number" in entry:
                    j += f"({entry['number']})"
            if "pages" in entry:
                j += f", {entry['pages']}"
            parts.append(j)
    elif etype in ("inproceedings", "incollection"):
        if "booktitle" in entry:
            bt = entry["booktitle"]
            if "volume" in entry:
                bt += f", {entry['volume']}"
            if "pages" in entry:
                bt += f", {entry['pages']}"
            parts.append(bt)
    elif etype == "book":
        if "publisher" in entry:
            parts.append(entry["publisher"])
    elif etype == "phdthesis":
        school = entry.get("school", "")
        parts.append(f"PhD dissertation, {school}" if school else "PhD dissertation")
    elif etype == "misc":
        if "howpublished" in entry:
            parts.append(entry["howpublished"])
    elif etype == "unpublished":
        if "note" in entry:
            parts.append(entry["note"])

    venue = ". ".join(parts) if parts else ""
    venue = venue.replace("--", "–")
    return venue


def source_link(path: str) -> str:
    return f"[source]({REPO}/{path.strip()})"


def cited_in_link(path: str) -> str:
    """Link to a Lean file that contains @cite{key}."""
    # path is like "Linglib/Foo/Bar.lean"
    rel = path.removeprefix("Linglib/")
    short = rel.removesuffix(".lean").rsplit("/", 1)[-1]
    return f"[{short}]({REPO}/{rel})"


def render_entry(entry: dict, cited_by: dict[str, list[str]]) -> str:
    authors = format_authors(entry.get("author", ""))
    year = entry.get("year", "")
    title = entry.get("title", "")
    venue = format_venue(entry)
    role = entry.get("role", "cited")
    sources_raw = entry.get("sources", "")
    sources = [s.strip() for s in sources_raw.split(";") if s.strip()]
    key = entry["_key"]

    line = f"**{authors}** ({year}). {title}."
    if venue:
        line += f" *{venue}*."
    line += "\\\n"
    badge = f"[{ROLE_BADGE.get(role, role)}]"
    parts = [badge]
    for s in sources:
        parts.append(source_link(s))
    line += " · ".join(parts)

    # Append "cited in" links from @cite{key} scan
    cite_files = cited_by.get(key, [])
    if cite_files:
        cite_links = [cited_in_link(f) for f in sorted(cite_files)]
        line += f"\\\ncited in: {', '.join(cite_links)}"

    return line


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    check_only = "--check" in sys.argv

    entries = parse_bib(BIB_PATH)
    bib_keys = {e["_key"] for e in entries}

    # Scan Lean files for @cite{key} references
    cited_by = scan_citations(LEAN_DIR)

    # Validate
    warnings = validate_citations(bib_keys, cited_by)
    for w in warnings:
        print(w, file=sys.stderr)

    cite_count = sum(len(files) for files in cited_by.values())
    valid_cites = sum(
        len(files) for key, files in cited_by.items() if key in bib_keys
    )
    print(
        f"Found {cite_count} @cite references "
        f"({valid_cites} valid, {cite_count - valid_cites} unknown)"
    )

    if check_only:
        sys.exit(1 if warnings else 0)

    # Group and sort
    grouped = defaultdict(list)
    for e in entries:
        sf = e.get("subfield", "")
        if sf:
            grouped[sf].append(e)

    for key in grouped:
        grouped[key].sort(
            key=lambda e: (e.get("author", "").lower(), e.get("year", ""))
        )

    lines = [
        "---",
        'title: "Bibliography"',
        "---",
        "",
        "Papers referenced, cited, or formalized in Linglib. "
        "Each entry links to the corresponding Lean source file.",
        "",
    ]

    for sf in SUBFIELD_ORDER:
        section_entries = grouped.get(sf, [])
        if not section_entries:
            continue
        label = SUBFIELD_LABELS.get(sf, sf)
        lines.append(f"## {label}")
        lines.append("")
        for e in section_entries:
            lines.append(render_entry(e, cited_by))
            lines.append("")

    OUT_PATH.write_text("\n".join(lines))
    print(f"Wrote {len(entries)} entries to {OUT_PATH}")


if __name__ == "__main__":
    main()
