# Raw Data Sources

This directory contains raw datasets used to generate Lean 4 modules in `Linglib/Core/`.
Generated files are checked into git alongside the raw data, so `lake build` works
without running any generation scripts. The scripts document the exact transformation
from raw data to Lean code and can be re-run to update or extend coverage.

## Organization

```
data/
  {source}-v{version}/    # versioned by upstream release
    *.csv / *.tsv          # raw data files
    README.md              # provenance, license, download instructions

scripts/
  gen_{source}.py          # generator: raw data → Lean modules

Linglib/Core/{Source}/     # generated output (checked in)
```

## Datasets

### WALS v2020.4

- **Source**: [World Atlas of Language Structures](https://wals.info/)
- **Format**: CLDF (Cross-Linguistic Data Formats) CSV
- **License**: CC BY 4.0
- **Citation**: Dryer, Matthew S. & Haspelmath, Martin (eds.) 2013. *WALS Online (v2020.3)*. Jena: Max Planck Institute for the Science of Human History. https://doi.org/10.5281/zenodo.7385533
- **Download**: https://doi.org/10.5281/zenodo.7385533 (wals-v2020.4.zip)
- **Generator**: `scripts/gen_wals.py`
- **Output**: `Linglib/Core/WALS/Features/F*.lean`, `Linglib/Core/WALS/Languages.lean`
- **Coverage**: Chapters 106A--111A (reciprocals, passives, antipassives, applicatives, causatives)

#### Regenerating

```bash
# All configured features
python3 scripts/gen_wals.py

# Specific features only
python3 scripts/gen_wals.py 106A 107A
```

After regenerating, run `lake build` to verify count theorems and grounding theorems still pass.
