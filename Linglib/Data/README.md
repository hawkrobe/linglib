# `Linglib/Data/` — typed datasets and example data

Three sibling directories at this level:

| Subdir | Purpose | Source format | Generated Lean |
|---|---|---|---|
| `Examples/` | Per-paper typed examples (`LinguisticExample` schema) | JSON, one file per paper | Inserted into study files via marker-block generator |
| `PHOIBLE/` | Cross-linguistic phonological inventories | CSV (raw under `PHOIBLE/raw/`) | `Inventories/{Lang}.lean` |
| `WALS/` | World Atlas of Language Structures | CSV (raw under `WALS/raw/`) | `Features/F*.lean`, `Languages.lean` |

Generated `.lean` files are checked in alongside the raw data so `lake build`
works without running any generation scripts. Generators document the
exact transformation and can be re-run to update or extend coverage.

## Layout convention

```
Linglib/Data/
  README.md                  # this file
  {SOURCE}/                  # PHOIBLE / WALS / ...
    Schema.lean              # typed Lean schema (where applicable)
    raw/                     # upstream raw data dump
    {generated subdirs}/     # generator output
  Examples/
    Schema.lean
    README.md                # JSON format + Leipzig conventions
    {AuthorYear}.json        # per-paper example data
```

## Datasets

### Examples — typed `LinguisticExample` data

See [`Examples/README.md`](Examples/README.md). Per-paper JSON; generator
inserts into Studies files via marker blocks. JSON (not CSV) because the
schema has nested fields.

### PHOIBLE 2.0

- **Source**: [PHOIBLE Online](https://phoible.org/) (Moran & McCloy 2019)
- **Format**: Single CSV (~23 MB, 105K rows)
- **License**: CC BY-SA 3.0
- **Citation**: Moran, Steven & McCloy, Daniel (eds.) 2019. *PHOIBLE 2.0*. Jena: Max Planck Institute for the Science of Human History. <http://phoible.org>. DOI: 10.5281/zenodo.2626687
- **Download**: <https://github.com/phoible/dev/blob/master/data/phoible.csv> (`PHOIBLE/raw/phoible.csv`)
- **Generator**: `scripts/gen_phoible.py`
- **Output**: `Linglib/Data/PHOIBLE/Inventories/{Lang}.lean`
- **Coverage**: 16 PhonProfile-aligned languages (English, German, Finnish, Turkish, Russian, French, Spanish, Japanese, Mandarin, Hindi/Urdu, Georgian, Hungarian, Swahili, Yoruba, Maori, Zulu); first inventory per ISO. Full 3000-inventory ingestion is a multi-session project.

#### Regenerating

```bash
python3 scripts/gen_phoible.py            # default 16 ISOs
python3 scripts/gen_phoible.py jpn ces    # specific ISOs
```

### WALS v2020.4

- **Source**: [World Atlas of Language Structures](https://wals.info/) (Dryer & Haspelmath, eds.)
- **Format**: CLDF (Cross-Linguistic Data Formats) CSV
- **License**: CC BY 4.0
- **Citation**: Dryer, Matthew S. & Haspelmath, Martin (eds.) 2013. *WALS Online (v2020.3)*. Jena: Max Planck Institute for the Science of Human History. <https://doi.org/10.5281/zenodo.7385533>
- **Download**: <https://doi.org/10.5281/zenodo.7385533> (wals-v2020.4.zip → `WALS/raw/`)
- **Generator**: `scripts/gen_wals.py`
- **Output**: `Linglib/Data/WALS/Features/F*.lean`, `Linglib/Data/WALS/Languages.lean`
- **Coverage**: Chapters 106A–111A (reciprocals, passives, antipassives, applicatives, causatives) and others; see Features directory.

#### Regenerating

```bash
python3 scripts/gen_wals.py            # all configured features
python3 scripts/gen_wals.py 106A 107A  # specific features only
```

After regenerating, run `lake build` to verify count theorems and
grounding theorems still pass.
