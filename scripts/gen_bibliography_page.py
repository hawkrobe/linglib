#!/usr/bin/env python3
"""Generate the browsable bibliography published at linglib.io/bibliography/.

Every entry of `references.bib` is shown with where linglib uses it. The places are read from
the repository, not from the entries' hand-kept `sources` fields: the `[key]` citations in the
tracked Lean files of `Linglib`, `Studies`, `Eval` and `Lab`, and the `bibkey` of the data files
under `Linglib/Data`. Each entry says whether its metadata has been checked against the
publication (`validated = {true}`), since an unchecked entry may be wrong. TeX accents are
rendered as Unicode; `--check` lists entries whose TeX the page cannot render.

Usage, from the repository root:

    python3 scripts/gen_bibliography_page.py            # write .lake/build/bibliography/index.html
    python3 scripts/gen_bibliography_page.py --out DIR  # write DIR/index.html
    python3 scripts/gen_bibliography_page.py --check    # report unrenderable TeX, exit 1 if any
"""

import argparse
import datetime
import html
import json
import os
import re
import subprocess
import sys
import unicodedata
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIB = ROOT / "references.bib"
TEMPLATE = ROOT / "scripts" / "bibliography_page" / "template.html"
SITE_CSS = ROOT / "scripts" / "site.css"
DEFAULT_OUT = ROOT / ".lake" / "build" / "bibliography"
LEAN_LIBS = ("Linglib", "Studies", "Eval", "Lab")
REPO = "https://github.com/linglib-community/linglib"
CITE = re.compile(r"\[([a-z0-9][a-z0-9-]*-\d{4}[a-z]?)\]")
BIBKEY = re.compile(r'"bibkey"\s*:\s*"([^"]+)"')


# ---------------------------------------------------------------- BibTeX


def parse_bib(text):
    """Entries of a BibTeX file as (type, key, fields), with brace-delimited, quoted and bare
    values. Lines starting with `%` are comments."""
    text = "\n".join(line for line in text.splitlines() if not line.lstrip().startswith("%"))
    entries = []
    for m in re.finditer(r"^\s*@(\w+)\s*\{\s*([^,\s]+)\s*,", text, re.M):
        kind = m.group(1).lower()
        if kind in ("comment", "string", "preamble"):
            continue
        i, fields = m.end(), {}
        while i < len(text):
            f = re.compile(r"\s*(\w+)\s*=\s*").match(text, i)
            if not f:
                break
            name, i = f.group(1).lower(), f.end()
            if text[i] == "{":
                depth, j = 1, i + 1
                while depth and j < len(text):
                    depth += {"{": 1, "}": -1}.get(text[j], 0)
                    j += 1
                value, i = text[i + 1:j - 1], j
            elif text[i] == '"':
                j = text.index('"', i + 1)
                value, i = text[i + 1:j], j + 1
            else:
                b = re.compile(r"[^,}\s]+").match(text, i)
                value, i = b.group(0), b.end()
            fields[name] = re.sub(r"\s+", " ", value).strip()
            c = re.compile(r"\s*,").match(text, i)
            if not c:
                break
            i = c.end()
        entries.append((kind, m.group(2), fields))
    return entries


ACCENTS = {"'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303",
           "=": "\u0304", ".": "\u0307", "u": "\u0306", "v": "\u030c", "H": "\u030b",
           "c": "\u0327", "k": "\u0328", "d": "\u0323", "r": "\u030a", "b": "\u0331"}
SPECIAL = {"ss": "ß", "ae": "æ", "AE": "Æ", "oe": "œ", "OE": "Œ", "aa": "å", "AA": "Å",
           "o": "ø", "O": "Ø", "l": "ł", "L": "Ł", "i": "ı", "j": "ȷ"}
# Named symbols, in text and in math mode.
SYMBOLS = {"dh": "ð", "DH": "Ð", "th": "þ", "TH": "Þ", "ng": "ŋ", "NG": "Ŋ", "S": "§",
           "textasciitilde": "~", "textquotedblleft": "“", "textquotedblright": "”",
           "textquoteleft": "‘", "textquoteright": "’", "ldots": "…", "dots": "…",
           "textendash": "–", "textemdash": "—", "textiota": "ι",
           "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
           "varepsilon": "ε", "zeta": "ζ", "eta": "η", "theta": "θ", "iota": "ι", "kappa": "κ",
           "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ", "pi": "π", "rho": "ρ", "sigma": "σ",
           "tau": "τ", "upsilon": "υ", "phi": "φ", "varphi": "φ", "chi": "χ", "psi": "ψ",
           "omega": "ω", "Gamma": "Γ", "Delta": "Δ", "Theta": "Θ", "Lambda": "Λ", "Xi": "Ξ",
           "Pi": "Π", "Sigma": "Σ", "Phi": "Φ", "Psi": "Ψ", "Omega": "Ω", "langle": "⟨",
           "rangle": "⟩", "star": "⋆", "forall": "∀", "exists": "∃", "neg": "¬", "wedge": "∧",
           "vee": "∨", "neq": "≠", "textschwa": "ə", "to": "→", "rightarrow": "→",
           "leftarrow": "←", "times": "×", "cdot": "·"}
ITAL_ON, ITAL_OFF = "\ue000", "\ue001"


def detex(s):
    """TeX as Unicode text, with italics marked for `tex_html`."""
    s = re.sub(r"\\(?:emph|textit|textsl)\s*\{", ITAL_ON + "{", s)
    s = re.sub(r"\{\\(?:em|it|itshape)\s+", ITAL_ON + "{", s)
    s = re.sub(r"\\(?:textsc|textrm|textup|textbf|textnormal|mbox|url|text)\s*\{", "{", s)
    for _ in range(3):
        s = re.sub(r"\\([`'^\"~=.])\s*\{?\s*\\?([A-Za-z])\s*\}?",
                   lambda m: m.group(2) + ACCENTS[m.group(1)], s)
        s = re.sub(r"\\([uvHckdrb])\s*\{\s*\\?([A-Za-z])\s*\}",
                   lambda m: m.group(2) + ACCENTS[m.group(1)], s)
        s = re.sub(r"\\([uvHckdrb]) ([A-Za-z])", lambda m: m.group(2) + ACCENTS[m.group(1)], s)
        s = re.sub(r"\\(ss|ae|AE|oe|OE|aa|AA|o|O|l|L|i|j)(?![A-Za-z])",
                   lambda m: SPECIAL[m.group(1)], s)
    s = re.sub(r"[\\@]cite\s*\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\textcommabelow\s*\{([A-Za-z])\}", "\\1\u0326", s)
    s = s.replace("\\\\", " ")
    s = re.sub(r"\\([A-Za-z]+)(?![A-Za-z])\s?",
               lambda m: SYMBOLS.get(m.group(1), m.group(0)), s)
    s = re.sub(r"\\[ ,;]", " ", s).replace("$", "")
    s = re.sub(r"\\([&%_#{}])", r"\1", s)
    s = s.replace("---", "—").replace("--", "–").replace("``", "“").replace("''", "”")
    s = s.replace("~", "\u00a0")
    # Close each italic span at the end of its braced group, then drop the braces.
    out, stack = [], []
    for i, ch in enumerate(s):
        if ch == "{":
            stack.append(i > 0 and s[i - 1] == ITAL_ON)
        elif ch == "}":
            if stack and stack.pop():
                out.append(ITAL_OFF)
        else:
            out.append(ch)
    return unicodedata.normalize("NFC", re.sub(r" {2,}", " ", "".join(out)))


def tex_html(s):
    return html.escape(detex(s)).replace(ITAL_ON, "<i>").replace(ITAL_OFF, "</i>")


def tex_text(s):
    return detex(s).replace(ITAL_ON, "").replace(ITAL_OFF, "")


def names(field):
    """Author or editor names as written: `Last, First` becomes `First Last`."""
    out = []
    for n in re.split(r"\s+and\s+", field):
        n = tex_text(n).strip()
        if n == "others":
            out.append("et al.")
        elif "," in n:
            last, first = n.split(",", 1)
            out.append(f"{first.strip()} {last.strip()}".strip())
        elif n:
            out.append(n)
    return out


def surname(field):
    """The family name of the first author or editor, for sorting."""
    first = re.split(r"\s+and\s+", field)[0]
    n = tex_text(first.split(",")[0] if "," in first else (first.split() or [""])[-1])
    return unicodedata.normalize("NFD", n).encode("ascii", "ignore").decode().lower()


def join_names(ns):
    if len(ns) <= 2:
        return " and ".join(ns)
    return ", ".join(ns[:-1]) + ", and " + ns[-1]


def venue(kind, f):
    """Where a work appeared, as HTML."""
    parts = []
    if kind == "article":
        j = tex_html(f.get("journal", ""))
        vol = f.get("volume", "")
        num = f"({f['number']})" if f.get("number") else ""
        parts.append(f"<i>{j}</i>" + (f" {html.escape(vol + num)}" if vol else ""))
    elif kind in ("incollection", "inproceedings", "inbook"):
        if f.get("booktitle"):
            ed = names(f.get("editor", ""))
            eds = f"{html.escape(join_names(ed))} (ed{'s' if len(ed) > 1 else ''}.), " if ed else ""
            parts.append(f"In {eds}<i>{tex_html(f['booktitle'])}</i>")
    elif kind in ("phdthesis", "mastersthesis"):
        label = "PhD thesis" if kind == "phdthesis" else "Master's thesis"
        parts.append(label + (", " + tex_html(f["school"]) if f.get("school") else ""))
    elif kind == "techreport":
        parts.append("Technical report" + (", " + tex_html(f["institution"])
                                           if f.get("institution") else ""))
    if f.get("pages"):
        parts.append(html.escape(tex_text(f["pages"])))
    published = kind in ("book", "incollection", "inbook")
    if published or (kind == "inproceedings" and f.get("publisher")):
        pub = ", ".join(tex_html(f[k]) for k in ("address", "publisher") if f.get(k))
        if pub:
            parts.append(pub)
    for k in ("howpublished", "note"):
        if f.get(k):
            parts.append(tex_html(f[k]))
    return ". ".join(p for p in parts if p)


# ---------------------------------------------------------------- where entries are used


def tracked_files():
    out = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True)
    return out.stdout.split()


def citations(keys):
    """For each key, the tracked files that use it: Lean files citing `[key]`, and data files
    with it as their `bibkey`."""
    used = defaultdict(set)
    for path in tracked_files():
        if path.endswith(".lean") and path.split("/")[0] in LEAN_LIBS:
            pattern = CITE
        elif path.endswith(".json") and path.startswith("Linglib/Data/"):
            pattern = BIBKEY
        else:
            continue
        try:
            text = (ROOT / path).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        for m in pattern.finditer(text):
            if m.group(1) in keys:
                used[m.group(1)].add(path)
    return used


def place(path, sha, docs_base):
    """A file that uses an entry, linked to its documentation or its source."""
    library = path.split("/")[0]
    if path.endswith(".lean"):
        href = docs_base + path[:-len(".lean")] + ".html"
    else:
        href = f"{REPO}/blob/{sha or 'main'}/{path}"
    return {"path": path, "library": library, "href": href}


# ---------------------------------------------------------------- page


def build(sha, docs_base):
    entries = parse_bib(BIB.read_text(encoding="utf-8"))
    used = citations({key for _, key, _ in entries})
    order = {"Studies": 0, "Eval": 1, "Lab": 2, "Linglib": 3}
    rows, unrendered = [], []
    for kind, key, f in entries:
        authors = join_names(names(f.get("author", "")))
        if not authors and f.get("editor"):
            eds = names(f["editor"])
            authors = join_names(eds) + (" (eds.)" if len(eds) > 1 else " (ed.)")
        title = tex_html(f.get("title", ""))
        ven = venue(kind, f)
        for field in ("author", "editor", "title", "journal", "booktitle", "publisher", "note"):
            if "\\" in tex_text(f.get(field, "")):
                unrendered.append((key, field, f[field]))
        places = sorted((place(p, sha, docs_base) for p in used.get(key, ())),
                        key=lambda p: (order.get(p["library"], 4), p["path"]))
        sub = f.get("subfield", "")
        rows.append({
            "key": key, "kind": kind, "authors": authors, "year": f.get("year", ""),
            "sort": [surname(f.get("author") or f.get("editor") or key), f.get("year", ""), key],
            "title": title, "venue": ven, "doi": f.get("doi", ""), "url": f.get("url", ""),
            "subfield": sub, "area": sub.split("/")[0].split(";")[0].strip() if sub else "",
            "checked": f.get("validated", "").lower() == "true", "places": places,
            "search": " ".join([key, tex_text(f.get("author", "")), tex_text(f.get("editor", "")),
                                f.get("year", ""), tex_text(f.get("title", "")),
                                tex_text(f.get("journal", "")), tex_text(f.get("booktitle", "")),
                                sub]).lower()})
    rows.sort(key=lambda r: r.pop("sort"))
    return rows, unrendered


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
    ap.add_argument("--docs-base", default="../docs/",
                    help="URL of the API documentation, relative to the page")
    ap.add_argument("--check", action="store_true",
                    help="report entries whose TeX the page cannot render, and write nothing")
    args = ap.parse_args()

    sha = git_commit()
    rows, unrendered = build(sha, args.docs_base)
    if args.check:
        for key, field, value in unrendered:
            print(f"{key}: {field} = {{{value}}}")
        print(f"{len(rows)} entries, {len(unrendered)} fields with TeX the page cannot render")
        sys.exit(1 if unrendered else 0)

    page = {"entries": rows, "built": datetime.date.today().isoformat(),
            "commit": {"sha": sha, "short": sha[:9],
                       "href": f"{REPO}/tree/{sha}" if sha else ""}}
    data = json.dumps(page, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    out = (TEMPLATE.read_text(encoding="utf-8")
           .replace("/*SITE_CSS*/", SITE_CSS.read_text(encoding="utf-8"))
           .replace("/*BIB_DATA*/{}", data))
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "index.html").write_text(out, encoding="utf-8")
    used = sum(1 for r in rows if r["places"])
    print(f"wrote {args.out / 'index.html'}: {len(rows)} entries, {used} used in the repository")


if __name__ == "__main__":
    main()
