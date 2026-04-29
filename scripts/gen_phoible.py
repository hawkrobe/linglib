#!/usr/bin/env python3
"""Generate Lean 4 modules from PHOIBLE 2.0 inventory data.

Usage:
    python3 scripts/gen_phoible.py [ISO_CODES...]

Examples:
    python3 scripts/gen_phoible.py eng deu jpn   # specific ISO codes
    python3 scripts/gen_phoible.py               # the 16 PhonProfile defaults

Reads from:  data/phoible-2019/phoible.csv
Writes to:   Linglib/Datasets/PHOIBLE/Inventories/{Name}.lean
             (one Lean file per requested ISO; first inventory per ISO).

The first inventory per ISO is taken (lowest InventoryID), which matches
PHOIBLE's canonical doculect pick. Multi-inventory languages (e.g. English
has 5 inventories in PHOIBLE) get only the canonical one.

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
DATA = ROOT / "data" / "phoible-2019" / "phoible.csv"
OUT  = ROOT / "Linglib" / "Datasets" / "PHOIBLE" / "Inventories"

# ── Default ISO set (the 16 PhonProfile languages from
#                    Phenomena/Phonology/Typology.lean) ──────────────────────

DEFAULT_ISOS = [
    "eng", "deu", "fin", "tur", "rus", "fra", "spa", "jpn",
    "cmn", "hin", "kat", "hun", "swh", "yor", "mri", "zul",
]

# ── PHOIBLE feature columns (in CSV order, matching Schema.lean) ───────────

# Special: "tone" and "stress" come right after Source; the 35 distinctive
# features begin at "syllabic". Order MUST match FeatureMatrix's field order.
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

# Lean reserved-word renames in FeatureMatrix.
COL_TO_FIELD = {
    "short": "short_",
    "long": "long_",
    "round": "round_",
}

# ── Helpers ────────────────────────────────────────────────────────────────

def feature_value(s: str) -> str:
    """Map a CSV cell value to a `FeatureValue` Lean constructor."""
    s = s.strip()
    if s == "+": return ".plus"
    if s == "-": return ".minus"
    if s == "0": return ".zero"
    # PHOIBLE sometimes uses "+,-" or "-,+" for variable values; treat as zero.
    return ".zero"

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

def emit_phoneme(row: dict) -> str:
    """Emit one Lean `Phoneme` literal."""
    # Build feature-matrix field assignments.
    feature_lines = []
    for col in FEATURE_COLS:
        field = COL_TO_FIELD.get(col, col)
        val = feature_value(row.get(col, "0"))
        feature_lines.append(f"        {field} := {val}")
    # tone + stress
    feature_lines.append(f"        tone := {feature_value(row.get('tone', '0'))}")
    feature_lines.append(f"        stress := {feature_value(row.get('stress', '0'))}")
    feature_block = ",\n".join(feature_lines)

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
      features := {{
{feature_block} }} }}"""

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

def emit_module(iso: str, rows_by_inv: dict, module_name: str) -> str:
    """Emit a complete Lean module for one ISO — uses first inventory."""
    if not rows_by_inv:
        raise ValueError(f"no inventories for {iso}")
    first_inv_id = min(rows_by_inv.keys())
    rows = rows_by_inv[first_inv_id]
    var_name = iso.lower()
    if not var_name.isidentifier():
        var_name = "lang"

    inv_block = emit_inventory(rows, var_name)
    n_phonemes = len(rows)
    head = rows[0]
    lang_name = head.get("LanguageName", "").strip().strip('"')

    return f"""import Linglib.Datasets.PHOIBLE.Schema

/-!
# PHOIBLE inventory: {lang_name} ({iso}, ID {first_inv_id})
@cite{{moran-mccloy-2019}}

Auto-generated from PHOIBLE 2.0 by `scripts/gen_phoible.py`.
**Do not edit by hand** — regenerate with `python3 scripts/gen_phoible.py {iso}`.

{n_phonemes} phonemes. PHOIBLE inventory ID {first_inv_id}, Glottocode `{head.get("Glottocode", "").strip().strip(chr(34))}`.
Source: PHOIBLE donor `{head.get("Source", "").strip().strip(chr(34))}`.
-/

namespace Datasets.PHOIBLE.Inventories.{module_name}

open Datasets.PHOIBLE

{inv_block}

end Datasets.PHOIBLE.Inventories.{module_name}
"""

# ── Main ───────────────────────────────────────────────────────────────────

def main():
    if not DATA.exists():
        sys.stderr.write(f"FATAL: {DATA} not found. Download with:\n")
        sys.stderr.write(f"  curl -sL https://raw.githubusercontent.com/phoible/dev/master/data/phoible.csv -o {DATA}\n")
        sys.exit(1)

    isos = sys.argv[1:] if len(sys.argv) > 1 else DEFAULT_ISOS
    isos = [iso.lower() for iso in isos]

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
        first_inv_id = min(invs.keys())
        head = invs[first_inv_id][0]
        lang_name = head.get("LanguageName", "").strip().strip('"')
        module_name = lang_module_name(lang_name, iso)

        out_path = OUT / f"{module_name}.lean"
        content = emit_module(iso, invs, module_name)
        out_path.write_text(content, encoding="utf-8")
        sys.stdout.write(f"[gen] {module_name}.lean ({len(invs[first_inv_id])} phonemes, ISO {iso}, InvID {first_inv_id})\n")

    sys.stdout.write(f"\nGenerated {len(isos)} modules under {OUT.relative_to(ROOT)}\n")

if __name__ == "__main__":
    main()
