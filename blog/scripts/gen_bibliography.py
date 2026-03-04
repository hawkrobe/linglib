#!/usr/bin/env python3
"""Generate blog/content/bibliography.md from blog/data/references.bib.

Also scans Lean source files for @cite{key} references, validates them
against the .bib, and appends a "cited in" reverse index to each entry.

Usage:
    python blog/scripts/gen_bibliography.py          # generate bibliography.md
    python blog/scripts/gen_bibliography.py --check   # validate only (no output)
"""

import json
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

# Maps each bib subfield value to a top-level tag.
# Entries with subfields not listed here go into "Other".
SUBFIELD_TO_TAG: dict[str, str] = {}

# Build mapping: any subfield starting with a known prefix maps to that tag.
_TAG_PREFIXES = {
    "pragmatics": "Pragmatics",
    "semantics":  "Semantics",
    "syntax":     "Syntax",
    "morphology": "Morphology",
    "phonology":  "Phonology",
    "comparative": "Other",
    "typology":   "Typology",
    "discourse":  "Other",
    "sociolinguistics": "Other",
    "psycholinguistics": "Other",
    "psychology": "Other",
    "psychometrics": "Other",
    "social-psychology": "Other",
    "philosophy": "Other",
    "logic":      "Other",
    "statistics": "Other",
    "linguistics": "Other",
    "acquisition": "Other",
}

# Display order for the tag buttons.
TAG_ORDER = ["Pragmatics", "Semantics", "Syntax", "Morphology",
             "Phonology", "Typology", "Other"]

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
    # Strip LaTeX formatting commands before brace removal
    val = re.sub(r"\\(?:emph|textit|textbf|textsc)\s*", "", val)
    # Strip braces (up to two levels of nesting)
    val = re.sub(r"\{([^{}]*)\}", r"\1", val)
    val = re.sub(r"\{([^{}]*)\}", r"\1", val)  # second pass for nested
    # Now resolve LaTeX accents on the braceless result
    # Use regex to handle backslash-command patterns reliably
    accent_map = [
        (r'\\"([uoaUOA])', lambda m: {"u":"ü","o":"ö","a":"ä","U":"Ü","O":"Ö","A":"Ä"}[m.group(1)]),
        (r"\\'([eEiIoOuUaA])", lambda m: {"e":"é","E":"É","i":"í","I":"Í","o":"ó","O":"Ó","u":"ú","U":"Ú","a":"á","A":"Á"}[m.group(1)]),
        (r"\\v\s*([zcsZCS])", lambda m: {"z":"ž","c":"č","s":"š","Z":"Ž","C":"Č","S":"Š"}[m.group(1)]),
        (r"\\c\s*([cC])", lambda m: {"c":"ç","C":"Ç"}[m.group(1)]),
    ]
    for pattern, repl in accent_map:
        val = re.sub(pattern, repl, val)
    val = val.replace("\\ss", "ß")
    val = val.replace("\\i", "ı")
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
            r"(\w[\w-]*)\s*=\s*\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}", body
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


def html_escape(text: str) -> str:
    """Escape HTML special characters."""
    return (text
            .replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace('"', "&quot;"))


def source_link_html(path: str) -> str:
    p = path.strip()
    return f'<a href="{REPO}/{p}">source</a>'


def cited_in_link_html(path: str) -> str:
    rel = path.removeprefix("Linglib/")
    short = rel.removesuffix(".lean").rsplit("/", 1)[-1]
    return f'<a href="{REPO}/{rel}">{html_escape(short)}</a>'


def resolve_tag(subfield: str) -> str:
    """Resolve a subfield string to its top-level tag."""
    # Check cache first
    if subfield in SUBFIELD_TO_TAG:
        return SUBFIELD_TO_TAG[subfield]
    # Try prefix matching
    for prefix, tag in _TAG_PREFIXES.items():
        if subfield == prefix or subfield.startswith(prefix + "/"):
            SUBFIELD_TO_TAG[subfield] = tag
            return tag
    # Handle compound subfields like "semantics/degree;semantics/tense;pragmatics"
    if ";" in subfield:
        first = subfield.split(";")[0].strip()
        return resolve_tag(first)
    SUBFIELD_TO_TAG[subfield] = "Other"
    return "Other"


def render_entry_html(entry: dict, cited_by: dict[str, list[str]]) -> str:
    """Render a single bibliography entry as an HTML div."""
    author_raw = entry.get("author", "") or entry.get("editor", "")
    authors = format_authors(author_raw)
    if not entry.get("author") and entry.get("editor"):
        authors += " (eds.)"
    year = entry.get("year", "")
    title = entry.get("title", "")
    venue = format_venue(entry)
    role = entry.get("role", "cited")
    sources_raw = entry.get("sources", "")
    sources = [s.strip() for s in sources_raw.split(";") if s.strip()]
    key = entry["_key"]
    tag = resolve_tag(entry.get("subfield", ""))

    # Build the entry HTML
    parts = []
    parts.append(f'<div class="bib-entry" data-key="{html_escape(key)}" data-role="{html_escape(role)}" data-tag="{html_escape(tag)}">')

    # Main citation line
    citation = f'<strong>{html_escape(authors)}</strong> ({html_escape(year)}). {html_escape(title)}.'
    if venue:
        citation += f' <em>{html_escape(venue)}</em>.'
    parts.append(f'<p class="bib-citation">{citation}</p>')

    # Metadata line: badge + source links + cited-in links
    badge = ROLE_BADGE.get(role, role)
    meta = f'<span class="bib-badge bib-badge-{html_escape(role)}">{html_escape(badge)}</span>'
    for s in sources:
        meta += f' · {source_link_html(s)}'

    cite_files = cited_by.get(key, [])
    if cite_files:
        cite_links = ", ".join(cited_in_link_html(f) for f in sorted(cite_files))
        meta += f'<br>cited in: {cite_links}'

    parts.append(f'<p class="bib-meta">{meta}</p>')
    parts.append('</div>')
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# Search bar HTML/CSS/JS
# ---------------------------------------------------------------------------

SEARCH_HTML = """\
<style>
.bib-toolbar {
  position: sticky;
  top: 0;
  z-index: 10;
  background: var(--theme);
  padding: 12px 0 8px;
  margin-bottom: 16px;
}
.bib-search-input {
  width: 100%;
  padding: 10px 14px;
  font-size: 1em;
  border: 2px solid var(--border);
  border-radius: 8px;
  background: var(--entry);
  color: var(--primary);
  outline: none;
  box-sizing: border-box;
}
.bib-search-input:focus {
  border-color: var(--secondary);
}
.bib-search-input::placeholder {
  color: var(--secondary);
  opacity: 0.7;
}
.bib-role-filters {
  display: flex;
  gap: 8px;
  margin-top: 8px;
  flex-wrap: wrap;
  align-items: center;
}
.bib-role-btn {
  padding: 4px 12px;
  font-size: 0.85em;
  border: 1.5px solid var(--border);
  border-radius: 6px;
  background: var(--entry);
  color: var(--secondary);
  cursor: pointer;
  transition: all 0.15s;
  font-family: inherit;
  line-height: 1.4;
}
.bib-role-btn:hover {
  border-color: var(--secondary);
}
.bib-role-btn.active[data-role="formalized"] {
  background: #22c55e20;
  border-color: #22c55e;
  color: #22c55e;
}
.bib-role-btn.active[data-role="foundational"] {
  background: #a78bfa20;
  border-color: #a78bfa;
  color: #a78bfa;
}
.bib-role-btn.active[data-role="cited"] {
  background: var(--entry);
  border-color: var(--primary);
  color: var(--primary);
}
.bib-search-status {
  font-size: 0.85em;
  color: var(--secondary);
  margin-top: 6px;
  min-height: 1.4em;
}
.bib-entry {
  margin-bottom: 1em;
}
.bib-entry.bib-hidden {
  display: none;
}
.bib-citation {
  margin: 0 0 2px;
  line-height: 1.5;
}
.bib-meta {
  margin: 0;
  font-size: 0.88em;
  color: var(--secondary);
  line-height: 1.5;
}
.bib-meta a {
  color: var(--secondary);
}
.bib-badge {
  font-weight: 600;
}
.bib-badge-formalized {
  color: #22c55e;
}
.bib-badge-foundational {
  color: #a78bfa;
}
.bib-badge-cited {
  color: var(--secondary);
}
.bib-tag-filters {
  display: flex;
  gap: 6px;
  margin-top: 6px;
  flex-wrap: wrap;
  align-items: center;
}
.bib-tag-btn {
  padding: 3px 10px;
  font-size: 0.82em;
  border: 1.5px solid var(--border);
  border-radius: 5px;
  background: var(--entry);
  color: var(--secondary);
  cursor: pointer;
  transition: all 0.15s;
  font-family: inherit;
  line-height: 1.4;
}
.bib-tag-btn:hover {
  border-color: var(--secondary);
}
.bib-tag-btn.active {
  background: var(--primary);
  border-color: var(--primary);
  color: var(--theme);
}
</style>

<div class="bib-toolbar">
  <input type="search" class="bib-search-input" id="bibSearchInput"
         placeholder="Search by author, title, year, or source path..."
         autocomplete="off" spellcheck="false">
  <div class="bib-role-filters">
    <button class="bib-role-btn active" data-role="formalized" id="bibRoleFormalized">formalized</button>
    <button class="bib-role-btn active" data-role="foundational" id="bibRoleFoundational">foundational</button>
    <button class="bib-role-btn" data-role="cited" id="bibRoleCited">cited</button>
  </div>
  <div class="bib-tag-filters" id="bibTagFilters"></div>
  <div class="bib-search-status" id="bibSearchStatus"></div>
</div>
"""


def search_script(
    index_json: str,
    role_counts: dict[str, int],
    tag_counts: dict[str, int],
) -> str:
    """Return the <script> block for search + role + tag filter functionality."""
    return f"""\
<script src="/linglib/js/fuse.basic.min.js"></script>
<script>
(function() {{
  var BIB_INDEX = {index_json};
  var ROLE_COUNTS = {json.dumps(role_counts)};
  var TAG_ORDER = {json.dumps(TAG_ORDER)};
  var TAG_COUNTS = {json.dumps(tag_counts)};

  var fuse = new Fuse(BIB_INDEX, {{
    keys: [
      {{ name: "a", weight: 0.4 }},
      {{ name: "t", weight: 0.3 }},
      {{ name: "y", weight: 0.15 }},
      {{ name: "s", weight: 0.15 }}
    ],
    threshold: 0.35,
    ignoreLocation: true,
    minMatchCharLength: 2
  }});

  var input = document.getElementById("bibSearchInput");
  var status = document.getElementById("bibSearchStatus");
  var allEntries = document.querySelectorAll(".bib-entry");
  var roleButtons = document.querySelectorAll(".bib-role-btn");
  var tagContainer = document.getElementById("bibTagFilters");

  // --- State ---
  var activeRoles = new Set(["formalized", "foundational"]);
  var activeTags = new Set();  // empty = show all tags

  // --- Build role button labels ---
  roleButtons.forEach(function(btn) {{
    var r = btn.dataset.role;
    if (ROLE_COUNTS[r] !== undefined) {{
      btn.textContent = r + " (" + ROLE_COUNTS[r] + ")";
    }}
  }});

  // --- Build tag buttons ---
  TAG_ORDER.forEach(function(tag) {{
    var count = TAG_COUNTS[tag] || 0;
    if (count === 0) return;
    var btn = document.createElement("button");
    btn.className = "bib-tag-btn";
    btn.dataset.tag = tag;
    btn.textContent = tag;
    btn.addEventListener("click", function() {{
      if (activeTags.has(tag)) {{
        activeTags.delete(tag);
        this.classList.remove("active");
      }} else {{
        activeTags.add(tag);
        this.classList.add("active");
      }}
      applyFilters();
    }});
    tagContainer.appendChild(btn);
  }});

  // --- Filtering ---
  function applyFilters() {{
    var query = input.value.trim();
    var searchKeys = null;

    if (query) {{
      var results = fuse.search(query);
      searchKeys = new Set(results.map(function(r) {{ return r.item.k; }}));
    }}

    var visibleCount = 0;
    var totalFiltered = 0;
    allEntries.forEach(function(el) {{
      var key = el.dataset.key;
      var role = el.dataset.role;
      var tag = el.dataset.tag;
      var matchesRole = activeRoles.has(role);
      var matchesTag = (activeTags.size === 0 || activeTags.has(tag));
      var matchesSearch = (searchKeys === null || searchKeys.has(key));
      if (matchesRole && matchesTag) totalFiltered++;
      if (matchesSearch && matchesRole && matchesTag) {{
        el.classList.remove("bib-hidden");
        visibleCount++;
      }} else {{
        el.classList.add("bib-hidden");
      }}
    }});

    // Update status text
    if (query) {{
      status.textContent = visibleCount + " of " + totalFiltered + " entries";
    }} else if (activeRoles.size < 3 || activeTags.size > 0) {{
      status.textContent = visibleCount + " entries shown";
    }} else {{
      status.textContent = "";
    }}
  }}

  // --- Role button handlers ---
  roleButtons.forEach(function(btn) {{
    btn.addEventListener("click", function() {{
      var role = this.dataset.role;
      if (activeRoles.has(role)) {{
        activeRoles.delete(role);
        this.classList.remove("active");
      }} else {{
        activeRoles.add(role);
        this.classList.add("active");
      }}
      applyFilters();
    }});
  }});

  // --- Search handler ---
  var debounceTimer;
  input.addEventListener("input", function() {{
    clearTimeout(debounceTimer);
    debounceTimer = setTimeout(applyFilters, 150);
  }});

  input.addEventListener("search", function() {{
    if (!this.value) applyFilters();
  }});

  // --- Initial filter ---
  applyFilters();
}})();
</script>
"""


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

    # Sort all entries alphabetically by author (or editor), then year
    entries.sort(key=lambda e: (
        (e.get("author") or e.get("editor") or "").lower(),
        e.get("year", ""),
    ))

    # Build search index and count roles/tags
    search_index = []
    role_counts: dict[str, int] = defaultdict(int)
    tag_counts: dict[str, int] = defaultdict(int)
    for e in entries:
        sources_raw = e.get("sources", "")
        sources = [s.strip() for s in sources_raw.split(";") if s.strip()]
        role = e.get("role", "cited")
        tag = resolve_tag(e.get("subfield", ""))
        search_index.append({
            "k": e["_key"],
            "a": format_authors(e.get("author") or e.get("editor") or ""),
            "t": e.get("title", ""),
            "y": e.get("year", ""),
            "s": " ".join(sources),
            "r": role,
        })
        role_counts[role] += 1
        tag_counts[tag] += 1

    index_json = json.dumps(search_index, ensure_ascii=False, separators=(",", ":"))

    lines = [
        "---",
        'title: "Bibliography"',
        "---",
        "",
        "Papers referenced, cited, or formalized in Linglib. "
        "Each entry links to the corresponding Lean source file.",
        "",
        SEARCH_HTML,
        "",
    ]

    # Flat list — all entries sorted by author
    for e in entries:
        lines.append(render_entry_html(e, cited_by))
        lines.append("")

    # Append search script at the end
    lines.append(search_script(index_json, dict(role_counts), dict(tag_counts)))

    OUT_PATH.write_text("\n".join(lines))
    print(f"Wrote {len(entries)} entries to {OUT_PATH}")


if __name__ == "__main__":
    main()
