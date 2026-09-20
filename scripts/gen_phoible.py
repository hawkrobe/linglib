#!/usr/bin/env python3
"""Generate Lean 4 modules from PHOIBLE 2.0 inventory data.

Usage:
    python3 scripts/gen_phoible.py [ISO_CODES...]
    python3 scripts/gen_phoible.py --chart [--check]

Examples:
    python3 scripts/gen_phoible.py eng deu jpn   # specific ISO codes
    python3 scripts/gen_phoible.py kor=2197      # a chosen inventory, by InventoryID
    python3 scripts/gen_phoible.py               # the 16 PhonProfile defaults
    python3 scripts/gen_phoible.py --chart       # the glyph-indexed feature chart

Reads from:  Linglib/Data/PHOIBLE/raw/phoible.csv
Writes to:   Linglib/Data/PHOIBLE/Inventories/{Name}.lean
             (one Lean file per requested ISO; first inventory per ISO).
             Linglib/Data/PHOIBLE/Chart.lean with `--chart`.

In PHOIBLE a glyph determines its feature values, whatever the inventory, so the chart has
one feature matrix per glyph. `--chart` fails if the CSV ever breaks that invariant. Tones
are left out, and so are glyphs with a contour value such as `-,+`, which a `Bool`-valued
matrix cannot hold.

The first inventory per ISO is taken (lowest InventoryID), which matches
PHOIBLE's canonical doculect pick, unless `ISO=ID` names another. A phoneme
whose glyph is in the chart takes its feature matrix from `Chart.lean`; tones
and contour-valued glyphs carry theirs inline.

Dependencies: pure stdlib (csv module).

Re-generation note: this script is non-destructive — it overwrites only the
files for ISO codes given on the command line.
"""

import csv
import re
import sys
from pathlib import Path
from collections import OrderedDict

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "Linglib" / "Data" / "PHOIBLE" / "raw" / "phoible.csv"
OUT  = ROOT / "Linglib" / "Data" / "PHOIBLE" / "Inventories"
CHART = ROOT / "Linglib" / "Data" / "PHOIBLE" / "Chart.lean"

# ── Default ISO set (the 16 PhonProfile languages from
#                    Phenomena/Phonology/Typology.lean) ──────────────────────

DEFAULT_ISOS = [
    "eng", "deu", "fin", "tur", "rus", "fra", "spa", "jpn",
    "cmn", "hin", "kat", "hun", "swh", "yor", "mri", "zul",
]

# ── PHOIBLE feature columns (in CSV order, matching Schema.lean) ───────────

# The distinctive-feature columns, with "tone" and "stress" appended when emitting.
FEATURE_COLS = [
    "syllabic", "short", "long", "consonantal", "sonorant", "continuant",
    "delayedRelease", "approximant", "tap", "trill", "nasal", "lateral",
    "labial", "round", "labiodental", "coronal", "anterior", "distributed",
    "strident", "dorsal", "high", "low", "front", "back", "tense",
    "retractedTongueRoot", "advancedTongueRoot", "periodicGlottalSource",
    "epilaryngealSource", "spreadGlottis", "constrictedGlottis", "fortis",
    "lenis", "raisedLarynxEjective", "loweredLarynxImplosive", "click",
]
# Plus tone + stress at the end.

# Column-to-constructor renames in `Data.PHOIBLE.Feature` (none at present).
COL_TO_FIELD = {}

# ── Helpers ────────────────────────────────────────────────────────────────

def feature_value(s: str):
    """Map a CSV cell value to a Lean `Bool`, or `None` for PHOIBLE's `0`."""
    s = s.strip()
    if s == "+": return "true"
    if s == "-": return "false"
    # "0" (not applicable), and the variable values "+,-" / "-,+", are unspecified.
    return None

def format_features(pairs, indent="        "):
    """Emit `Bundle.ofList [...]` over the specified (feature, value) pairs."""
    items = [f"(.{f}, {v})" for f, v in pairs]
    lines = []; cur = indent
    for it in items:
        piece = (it if cur.strip() == "" else ", " + it)
        if len(cur) + len(piece) + 1 > 96:
            lines.append(cur + ","); cur = indent + it
        else:
            cur += piece if cur.strip() else it
    lines.append(cur)
    return "Bundle.ofList [" + chr(10) + chr(10).join(lines) + "]"

def segment_class(s: str) -> str:
    s = s.strip().strip('"')
    if s == "consonant": return ".consonant"
    if s == "vowel": return ".vowel"
    if s == "tone": return ".tone"
    raise ValueError(f"unknown segment class {s!r}")

def source_constructor(s: str) -> str:
    s = s.strip().strip('"').lower()
    # Map PHOIBLE source codes to Schema.Source constructors.
    mapping = {
        "spa": ".spa",
        "upsid": ".upsid",
        "aa": ".aa",
        "gm": ".gm",
        "ph": ".ph",
        "ra": ".ra",
        "saphon": ".saphon",
        "ea": ".ea",
        "er": ".er",
    }
    return mapping.get(s, ".upsid")  # fallback

def lean_string(s: str) -> str:
    """Quote a string for Lean source. Escapes backslashes and quotes."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

def parse_allophones(s: str) -> list:
    s = s.strip().strip('"')
    if s == "NA" or s == "": return []
    return s.split()

def lang_module_name(lang_name: str, iso: str) -> str:
    """Lean module name from PHOIBLE LanguageName + ISO. Title-case, ASCII only."""
    name = lang_name.strip().strip('"')
    # Strip parentheses, special chars; collapse spaces.
    name = re.sub(r'\(.*?\)', '', name)
    name = re.sub(r'[^A-Za-z0-9]+', ' ', name).strip()
    parts = name.split()
    if not parts:
        return iso.upper()
    # Title-case first letter of each word, ASCII fallback.
    title = "".join(p[:1].upper() + p[1:].lower() for p in parts)
    # Lean module names need to be valid identifiers.
    if not title or not title[0].isalpha():
        return iso.upper()
    return title

# ── Per-inventory emission ─────────────────────────────────────────────────

def in_chart(row: dict) -> bool:
    """Whether the chart has this row's glyph: not a tone, no contour value."""
    return (row["SegmentClass"] != "tone"
            and not any("," in row[c] for c in FEATURE_COLS + ["tone", "stress"]))

def emit_phoneme(row: dict) -> str:
    """Emit one Lean `Phoneme` literal."""
    if in_chart(row):
        feature_block = f".«{row['Phoneme']}»"
    else:
        pairs = []
        for col in FEATURE_COLS + ["tone", "stress"]:
            val = feature_value(row.get(col, "0"))
            if val is not None:
                pairs.append((COL_TO_FIELD.get(col, col), val))
        feature_block = format_features(pairs)

    glyph = row.get("Phoneme", "").strip().strip('"')
    glyph_id = row.get("GlyphID", "").strip().strip('"')
    allo = parse_allophones(row.get("Allophones", ""))
    marginal = row.get("Marginal", "").strip().strip('"') == "+"
    seg_cls = segment_class(row.get("SegmentClass", "consonant"))

    allo_str = "[" + ", ".join(lean_string(a) for a in allo) + "]"

    return f"""    {{ glyph := {lean_string(glyph)},
      glyphId := {lean_string(glyph_id)},
      allophones := {allo_str},
      marginal := {str(marginal).lower()},
      segmentClass := {seg_cls},
      features := {feature_block} }}"""

def emit_inventory(rows: list, var_name: str) -> str:
    """Emit one Lean `Inventory` literal for a list of CSV rows."""
    if not rows:
        raise ValueError("empty rows")
    head = rows[0]
    inv_id = int(head["InventoryID"])
    glottocode = head.get("Glottocode", "").strip().strip('"')
    iso = head.get("ISO6393", "").strip().strip('"')
    lang_name = head.get("LanguageName", "").strip().strip('"')
    dialect_raw = head.get("SpecificDialect", "").strip().strip('"')
    dialect = "" if dialect_raw == "NA" else dialect_raw
    src = source_constructor(head.get("Source", "upsid"))

    phoneme_blocks = ",\n".join(emit_phoneme(r) for r in rows)

    return f"""def {var_name} : Inventory :=
  {{ id := {inv_id},
    glottocode := {lean_string(glottocode)},
    iso := {lean_string(iso)},
    languageName := {lean_string(lang_name)},
    specificDialect := {lean_string(dialect)},
    source := {src},
    phonemes := [
{phoneme_blocks} ] }}"""

def emit_module(iso: str, rows_by_inv: dict, module_name: str, inv_id=None) -> str:
    """Emit a complete Lean module for one ISO: the chosen inventory, else the first."""
    if not rows_by_inv:
        raise ValueError(f"no inventories for {iso}")
    first_inv_id = min(rows_by_inv.keys()) if inv_id is None else inv_id
    rows = rows_by_inv[first_inv_id]
    var_name = iso.lower()
    if not var_name.isidentifier():
        var_name = "lang"

    inv_block = emit_inventory(rows, var_name)
    n_phonemes = len(rows)
    head = rows[0]
    lang_name = head.get("LanguageName", "").strip().strip('"')

    regen = iso if inv_id is None else f"{iso}={inv_id}"
    return f"""import Linglib.Data.PHOIBLE.Chart

/-!
# PHOIBLE inventory: {lang_name} ({iso}, ID {first_inv_id})
[moran-mccloy-2019]

Auto-generated from PHOIBLE 2.0 by `scripts/gen_phoible.py`.
**Do not edit by hand** — regenerate with `python3 scripts/gen_phoible.py {regen}`.

{n_phonemes} phonemes. PHOIBLE inventory ID {first_inv_id}, Glottocode `{head.get("Glottocode", "").strip().strip(chr(34))}`.
Source: PHOIBLE donor `{head.get("Source", "").strip().strip(chr(34))}`.
-/

namespace Data.PHOIBLE.Inventories.{module_name}

open Data.PHOIBLE

{inv_block}

end Data.PHOIBLE.Inventories.{module_name}
"""

# ── The glyph chart ────────────────────────────────────────────────────────

def chart_rows():
    """One CSV row per glyph, in order of first appearance; checks that a glyph
    determines its feature values."""
    cols = FEATURE_COLS + ["tone", "stress"]
    first = OrderedDict()
    with open(DATA, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            glyph = row["Phoneme"]
            vec = tuple(row[c] for c in cols)
            seen = first.get(glyph)
            if seen is None:
                first[glyph] = (row, vec)
            elif seen[1] != vec:
                sys.exit(f"FATAL: glyph {glyph!r} has two feature vectors")
    return [row for row, _ in first.values()]

def emit_chart() -> str:
    cols = FEATURE_COLS + ["tone", "stress"]
    entries = []
    skipped_tone = skipped_contour = 0
    for row in sorted(chart_rows(), key=lambda r: r["GlyphID"]):
        if row["SegmentClass"] == "tone":
            skipped_tone += 1; continue
        if any("," in row[c] for c in cols):
            skipped_contour += 1; continue
        glyph = row["Phoneme"]
        if "»" in glyph or "-/" in glyph:
            sys.exit(f"FATAL: glyph {glyph!r} cannot be quoted")
        pairs = [(COL_TO_FIELD.get(c, c), feature_value(row[c])) for c in cols]
        pairs = [(f, v) for f, v in pairs if v is not None]
        block = format_features(pairs, indent="  ")
        entries.append(
            f"/-- {glyph} (GlyphID {row['GlyphID']}), {row['SegmentClass']}. -/\n"
            f"def «{glyph}» : FeatureMatrix := {block}")
    body = "\n\n".join(entries)
    return f"""import Linglib.Data.PHOIBLE.Schema

/-!
# PHOIBLE feature chart

This file lists the feature matrix PHOIBLE 2.0 assigns to each segment glyph. In PHOIBLE a
glyph determines its feature values in every inventory that uses it, so one matrix per glyph
is the whole of the database's feature information. Each matrix is a constant named by its
glyph in the namespace of `FeatureMatrix`, so that `.«n»` and `.«t̠ʃ»` are feature matrices
wherever one is expected. A feature PHOIBLE marks `0`, not applicable, is left unspecified.

The chart has {len(entries)} glyphs. It omits the {skipped_tone} tones and the {skipped_contour} glyphs with a contour
value such as `-,+`, the prenasalized, secondarily articulated and click segments and the
diphthongs, which a two-valued matrix cannot hold.

Auto-generated by `scripts/gen_phoible.py --chart`. **Do not edit by hand.**

## References

* [moran-mccloy-2019]
-/

namespace Data.PHOIBLE.FeatureMatrix

{body}

end Data.PHOIBLE.FeatureMatrix
"""

# ── Main ───────────────────────────────────────────────────────────────────

def main():
    if not DATA.exists():
        sys.stderr.write(f"FATAL: {DATA} not found. Download with:\n")
        sys.stderr.write(f"  curl -sL https://raw.githubusercontent.com/phoible/dev/master/data/phoible.csv -o {DATA}\n")
        sys.exit(1)

    if sys.argv[1:] == ["--chart", "--check"]:
        if not CHART.exists() or CHART.read_text(encoding="utf-8") != emit_chart():
            sys.exit(f"FAIL: {CHART.relative_to(ROOT)} is out of sync; run --chart")
        sys.stdout.write(f"OK: {CHART.relative_to(ROOT)} is in sync\n")
        return
    if sys.argv[1:] == ["--chart"]:
        content = emit_chart()
        CHART.write_text(content, encoding="utf-8")
        sys.stdout.write(f"[gen] {CHART.relative_to(ROOT)} ({content.count(chr(10))} lines)\n")
        return

    args = sys.argv[1:] if len(sys.argv) > 1 else DEFAULT_ISOS
    chosen = {}
    for a in args:
        iso, _, inv = a.lower().partition("=")
        chosen[iso] = int(inv) if inv else None
    isos = list(chosen)

    OUT.mkdir(parents=True, exist_ok=True)

    # First pass: collect rows per (ISO, InventoryID).
    by_iso = {iso: OrderedDict() for iso in isos}
    with open(DATA, encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            iso = row.get("ISO6393", "").strip().strip('"').lower()
            if iso not in by_iso:
                continue
            inv_id = int(row["InventoryID"])
            by_iso[iso].setdefault(inv_id, []).append(row)

    # Emit one module per requested ISO.
    for iso in isos:
        invs = by_iso[iso]
        if not invs:
            sys.stderr.write(f"WARN: no rows for ISO {iso}; skipping\n")
            continue
        first_inv_id = min(invs.keys()) if chosen[iso] is None else chosen[iso]
        if first_inv_id not in invs:
            sys.exit(f"FATAL: ISO {iso} has no inventory {first_inv_id}; it has {sorted(invs)}")
        head = invs[first_inv_id][0]
        lang_name = head.get("LanguageName", "").strip().strip('"')
        module_name = lang_module_name(lang_name, iso)

        out_path = OUT / f"{module_name}.lean"
        content = emit_module(iso, invs, module_name, chosen[iso])
        out_path.write_text(content, encoding="utf-8")
        sys.stdout.write(f"[gen] {module_name}.lean ({len(invs[first_inv_id])} phonemes, ISO {iso}, InvID {first_inv_id})\n")

    sys.stdout.write(f"\nGenerated {len(isos)} modules under {OUT.relative_to(ROOT)}\n")

if __name__ == "__main__":
    main()
