#!/usr/bin/env python3
"""Generate Lean 4 modules from WALS CLDF data.

Usage:
    python3 scripts/gen_wals.py [FEATURE_IDS...]

Examples:
    python3 scripts/gen_wals.py 106A 107A 108A    # specific features
    python3 scripts/gen_wals.py                     # all configured features

Reads from:  data/wals-v2020.4/*.csv
Writes to:   Linglib/Core/WALS/Features/F{ID}.lean
             Linglib/Core/WALS/Languages.lean
"""

import csv
import re
import sys
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data" / "wals-v2020.4"
OUT  = ROOT / "Linglib" / "Core" / "WALS"

# ── Feature configuration ───────────────────────────────────────────────────
# Maps WALS feature ID → (Lean enum name, { WALS code number → Lean constructor })
# Constructor names are manually curated for readability.

FEATURES = {
    "106A": {
        "name": "Reciprocal Constructions",
        "chapter": 106,
        "enum": "ReciprocalType",
        "author": "maslova-nedjalkov-2013",
        "values": {
            1: ("noReciprocalConstruction", "No reciprocal construction"),
            2: ("distinctFromReflexive", "Distinct from reflexive"),
            3: ("mixed", "Mixed"),
            4: ("identicalToReflexive", "Identical to reflexive"),
        },
    },
    "107A": {
        "name": "Passive Constructions",
        "chapter": 107,
        "enum": "PassiveType",
        "author": "siewierska-2013",
        "values": {
            1: ("present", "Present"),
            2: ("absent", "Absent"),
        },
    },
    "108A": {
        "name": "Antipassive Constructions",
        "chapter": 108,
        "enum": "AntipassiveType",
        "author": "polinsky-2013",
        "values": {
            1: ("implicitPatient", "Implicit patient"),
            2: ("obliquePatient", "Oblique patient"),
            3: ("noAntipassive", "No antipassive"),
        },
    },
    "108B": {
        "name": "Productivity of the Antipassive Construction",
        "chapter": 108,
        "enum": "AntipassiveProductivity",
        "author": "polinsky-2013",
        "values": {
            1: ("productive", "Productive"),
            2: ("partiallyProductive", "Partially productive"),
            3: ("notProductive", "Not productive"),
            4: ("noAntipassive", "No antipassive"),
        },
    },
    "109A": {
        "name": "Applicative Constructions",
        "chapter": 109,
        "enum": "ApplicativeType",
        "author": "polinsky-2013",
        "values": {
            1: ("benefactiveBothBases", "Benefactive object; both bases"),
            2: ("benefactiveTransOnly", "Benefactive object; only transitive"),
            3: ("benefactiveAndOtherBothBases", "Benefactive and other; both bases"),
            4: ("benefactiveAndOtherTransOnly", "Benefactive and other; only transitive"),
            5: ("nonBenefactiveBothBases", "Non-benefactive object; both bases"),
            6: ("nonBenefactiveTransOnly", "Non-benefactive object; only transitive"),
            7: ("nonBenefactiveIntransOnly", "Non-benefactive object; only intransitive"),
            8: ("noApplicative", "No applicative construction"),
        },
    },
    "109B": {
        "name": "Other Roles of Applied Objects",
        "chapter": 109,
        "enum": "AppliedObjectRole",
        "author": "polinsky-2013",
        "values": {
            1: ("instrument", "Instrument"),
            2: ("locative", "Locative"),
            3: ("instrumentAndLocative", "Instrument and locative"),
            4: ("onlyBenefactive", "No other roles (= Only benefactive)"),
            5: ("noApplicative", "No applicative construction"),
        },
    },
    "110A": {
        "name": "Periphrastic Causative Constructions",
        "chapter": 110,
        "enum": "PeriphrasticCausativeType",
        "author": "song-2013",
        "values": {
            1: ("sequentialOnly", "Sequential but no purposive"),
            2: ("purposiveOnly", "Purposive but no sequential"),
            3: ("both", "Both"),
        },
    },
    "111A": {
        "name": "Nonperiphrastic Causative Constructions",
        "chapter": 111,
        "enum": "NonperiphrCausativeType",
        "author": "song-2013",
        "values": {
            1: ("neither", "Neither"),
            2: ("morphologicalOnly", "Morphological but no compound"),
            3: ("compoundOnly", "Compound but no morphological"),
            4: ("both", "Both"),
        },
    },
}


def load_languages():
    """Load WALS language metadata."""
    langs = {}
    with open(DATA / "languages.csv", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            langs[row["ID"]] = {
                "name": row["Name"],
                "iso": row["ISO639P3code"],
                "family": row["Family"],
                "genus": row["Genus"],
            }
    return langs


def load_values(feature_id):
    """Load all datapoints for a given WALS feature."""
    entries = []
    with open(DATA / "values.csv", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row["Parameter_ID"] == feature_id:
                entries.append({
                    "language_id": row["Language_ID"],
                    "value": int(row["Value"]),
                })
    return entries


def lean_safe_string(s):
    """Escape a string for use in Lean string literals."""
    return s.replace("\\", "\\\\").replace('"', '\\"')


def to_lean_id(name):
    """Convert a language name to a valid Lean identifier."""
    # Remove parenthetical qualifiers, keep only alphanumeric + underscore
    s = re.sub(r"\s*\(.*?\)", "", name)
    s = re.sub(r"[''ʼ]", "", s)
    s = re.sub(r"[^a-zA-ZÀ-ÿ0-9]", "_", s)
    s = re.sub(r"_+", "_", s).strip("_")
    # Lean identifiers must start with lowercase
    if s and s[0].isupper():
        s = s[0].lower() + s[1:]
    return s


def generate_feature(feature_id, langs):
    """Generate a Lean module for a single WALS feature."""
    cfg = FEATURES[feature_id]
    entries = load_values(feature_id)
    entries.sort(key=lambda e: langs.get(e["language_id"], {}).get("name", ""))

    # Count per value
    counts = defaultdict(int)
    for e in entries:
        counts[e["value"]] += 1

    lines = []
    fid_clean = feature_id.replace("A", "A").replace("B", "B")

    # Module docstring
    lines.append(f'/-!')
    lines.append(f'# WALS Feature {feature_id}: {cfg["name"]}')
    lines.append(f'@cite{{{cfg["author"]}}}')
    lines.append(f'')
    lines.append(f'Auto-generated from WALS v2020.4 CLDF data.')
    lines.append(f'**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py {feature_id}`.')
    lines.append(f'')
    lines.append(f'Chapter {cfg["chapter"]}, {len(entries)} languages.')
    lines.append(f'-/')
    lines.append(f'')
    lines.append(f'namespace Core.WALS.F{fid_clean}')
    lines.append(f'')

    # Value enum
    lines.append(f'/-- WALS {feature_id} values. -/')
    lines.append(f'inductive {cfg["enum"]} where')
    for num in sorted(cfg["values"]):
        ctor, desc = cfg["values"][num]
        lines.append(f'  | {ctor}  -- {desc} ({counts.get(num, 0)} languages)')
    lines.append(f'  deriving DecidableEq, BEq, Repr')
    lines.append(f'')

    # Datapoint structure
    lines.append(f'/-- A single WALS {feature_id} datapoint. -/')
    lines.append(f'structure Datapoint where')
    lines.append(f'  walsCode : String')
    lines.append(f'  language : String')
    lines.append(f'  iso : String')
    lines.append(f'  value : {cfg["enum"]}')
    lines.append(f'  deriving Repr, BEq, DecidableEq')
    lines.append(f'')

    # Data
    lines.append(f'/-- Complete WALS {feature_id} dataset ({len(entries)} languages). -/')
    lines.append(f'def allData : List Datapoint :=')

    for i, entry in enumerate(entries):
        lang = langs.get(entry["language_id"], {})
        name = lean_safe_string(lang.get("name", "?"))
        iso = lang.get("iso", "")
        wals_code = entry["language_id"]
        ctor, _ = cfg["values"][entry["value"]]
        prefix = "  [" if i == 0 else "  ,"
        lines.append(f'{prefix} {{ walsCode := "{wals_code}", language := "{name}", iso := "{iso}", value := .{ctor} }}')

    lines.append(f'  ]')
    lines.append(f'')

    # Count verification theorems
    lines.append(f'-- Count verification')
    lines.append(f'theorem total_count : allData.length = {len(entries)} := by native_decide')
    lines.append(f'')
    for num in sorted(cfg["values"]):
        ctor, desc = cfg["values"][num]
        count = counts.get(num, 0)
        lines.append(
            f'theorem count_{ctor} :'
        )
        lines.append(
            f'    (allData.filter (·.value == .{ctor})).length = {count} := by native_decide'
        )
    lines.append(f'')

    # Lookup function
    lines.append(f'/-- Look up a language by WALS code. -/')
    lines.append(f'def lookup (code : String) : Option Datapoint :=')
    lines.append(f'  allData.find? (·.walsCode == code)')
    lines.append(f'')
    lines.append(f'/-- Look up a language by ISO 639-3 code. -/')
    lines.append(f'def lookupISO (iso : String) : Option Datapoint :=')
    lines.append(f'  allData.find? (·.iso == iso)')
    lines.append(f'')

    lines.append(f'end Core.WALS.F{fid_clean}')
    lines.append(f'')

    return "\n".join(lines)


def generate_languages(langs, used_ids):
    """Generate the shared Languages module."""
    # Only include languages that appear in at least one generated feature
    used_langs = {lid: langs[lid] for lid in sorted(used_ids) if lid in langs}

    lines = []
    lines.append('/-!')
    lines.append('# WALS Language Metadata')
    lines.append('')
    lines.append('Auto-generated from WALS v2020.4 CLDF data.')
    lines.append('**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py`.')
    lines.append('')
    lines.append(f'{len(used_langs)} languages referenced across generated features.')
    lines.append('-/')
    lines.append('')
    lines.append('namespace Core.WALS')
    lines.append('')
    lines.append('/-- WALS language metadata. -/')
    lines.append('structure Language where')
    lines.append('  walsCode : String')
    lines.append('  name : String')
    lines.append('  iso : String')
    lines.append('  family : String')
    lines.append('  genus : String')
    lines.append('  deriving Repr, BEq, DecidableEq')
    lines.append('')
    lines.append(f'/-- All languages referenced in generated WALS features ({len(used_langs)}). -/')
    lines.append('def languages : List Language :=')

    for i, (lid, lang) in enumerate(sorted(used_langs.items(), key=lambda x: x[1]["name"])):
        name = lean_safe_string(lang["name"])
        iso = lang["iso"]
        family = lean_safe_string(lang["family"])
        genus = lean_safe_string(lang["genus"])
        prefix = "  [" if i == 0 else "  ,"
        lines.append(
            f'{prefix} {{ walsCode := "{lid}", name := "{name}", iso := "{iso}", '
            f'family := "{family}", genus := "{genus}" }}'
        )

    lines.append('  ]')
    lines.append('')
    lines.append('/-- Look up a language by WALS code. -/')
    lines.append('def findLanguage (code : String) : Option Language :=')
    lines.append('  languages.find? (·.walsCode == code)')
    lines.append('')
    lines.append('end Core.WALS')
    lines.append('')

    return "\n".join(lines)


def main():
    feature_ids = sys.argv[1:] if len(sys.argv) > 1 else list(FEATURES.keys())

    # Validate
    for fid in feature_ids:
        if fid not in FEATURES:
            print(f"Error: unknown feature {fid}. Known: {', '.join(FEATURES.keys())}")
            sys.exit(1)

    print(f"Loading WALS data from {DATA}")
    langs = load_languages()
    print(f"  {len(langs)} languages loaded")

    used_language_ids = set()

    for fid in feature_ids:
        cfg = FEATURES[fid]
        print(f"Generating {fid}: {cfg['name']}...")
        content = generate_feature(fid, langs)

        # Collect used language IDs
        entries = load_values(fid)
        for e in entries:
            used_language_ids.add(e["language_id"])

        out_path = OUT / "Features" / f"F{fid}.lean"
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(content, encoding="utf-8")
        print(f"  → {out_path.relative_to(ROOT)} ({len(entries)} entries)")

    # Generate Languages module
    print("Generating Languages.lean...")
    content = generate_languages(langs, used_language_ids)
    out_path = OUT / "Languages.lean"
    out_path.write_text(content, encoding="utf-8")
    print(f"  → {out_path.relative_to(ROOT)} ({len(used_language_ids)} languages)")

    print("Done.")


if __name__ == "__main__":
    main()
