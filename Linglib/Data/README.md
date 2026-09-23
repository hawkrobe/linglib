# `Linglib/Data/` — typed datasets and example data

Three sibling directories at this level:

| Subdir | Purpose | Source format | Generated Lean |
|---|---|---|---|
| `Examples/` | Per-paper typed examples (`LinguisticExample` schema) | JSON, one file per paper | Inserted into study files via marker-block generator |
| `Experiments/` | Per-paper experimental results (stimulus coding, printed statistics) | JSON, one file per paper | `Experiments/{AuthorYear}.lean` |
| `Forms/` | Per-paper CLDF word forms (`FormTable`, `ParameterTable`, custom `FormRelationTable`) | JSON, one file per paper | `Forms/{AuthorYear}.lean` |
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

### Forms — CLDF word-level data

Per-paper word forms in the Cross-Linguistic Data Formats Wordlist shape: a
`FormTable` (form, language, concept, segmentation, source), a
`ParameterTable` (the concepts), and a linglib extension `FormRelationTable`
for the paradigmatic pairs a paper asserts (stem and past, adjective and
comparative, base and reduplicant). A `FormTable` row may carry custom
columns, which CLDF permits in any table, for the per-form codes a paper
assigns; they are emitted into the form's `columns`. The morphological
counterpart of `Examples/`, whose datum is a sentence and its gloss.

- **Schema**: `Linglib/Data/Forms/Schema.lean`
- **Generator**: `scripts/gen_forms.py` (`--check` verifies sync, `--fmt` canonical JSON)
- **Input/Output**: `Linglib/Data/Forms/{AuthorYear}.json` → `{AuthorYear}.lean`

### Treebank coverage of non-projectivity constraints

Per-paper statistics on how many of a treebank's dependency trees, or of the grammar rules
extracted from them, satisfy a constraint on non-projectivity (projectivity, a gap-degree
bound, well-nestedness, planarity, or a conjunction), at the precision the paper prints.

- **Schema**: `Linglib/Data/Treebank/Coverage/Schema.lean`
- **Generator**: `scripts/gen_treebank_coverage.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/Treebank/Coverage/{Paper}.json` → `{Paper}.lean`

### Experimental results

The results a paper prints for its experiments, one table per printed table: the stimulus
inventory with its coding, the design constants, and the statistics (shares of ceiling ratings,
counts, means) at the precision the paper prints them, as `Decimal`s that keep the printed
digits. A paper's coding labels (its factors, predictors, response types) are generated enums; a
study maps them into its theory types by total functions and defines there what it concludes
from the numbers (a prototype, a preference, a significant difference). Each table records its
locator and whether it was checked against the page images, and a row may carry a note on how
it departs from the print.

The released data behind a paper, where there is any, is linked from its JSON (`meta.rawData`)
and the generated module's docstring, but not committed: the tables stay at the granularity the
paper argues at. A table the authors' data reproduces is marked `raw-data`, and
`scripts/check_experiments.py <Paper>` downloads the data and recomputes it through
`scripts/experiments/<Paper>.py`.

- **Schema**: `Linglib/Data/Experiments/Schema.lean`
- **Generator**: `scripts/gen_experiments.py` (`--check` verifies sync; the column vocabulary is
  in its docstring)
- **Raw-data check**: `scripts/check_experiments.py` (needs network access; run by hand)
- **Input/Output**: `Linglib/Data/Experiments/{Paper}.json` → `{Paper}.lean`

### UD dependency length by language

Per-paper corpus statistics over Universal Dependencies treebanks: the
proportion of head-final dependencies and the mean dependency length per word
at fixed sentence lengths, as a paper prints them (values as scaled integers).

- **Schema**: `Linglib/Data/UD/DependencyLength/Schema.lean`
- **Generator**: `scripts/gen_ud_deplength.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/UD/DependencyLength/{Paper}.json` → `{Paper}.lean`

### Hiatus resolution samples

A paper's survey of which vowel elides where two vowels meet: for each language of the sample,
the kind of juncture (two lexical words, a lexical word before a function word, a prefix before
a root, a root before a suffix) and the vowel that elides there, with the reports the paper
marks as uncertain flagged.

- **Schema**: `Linglib/Data/Hiatus/Schema.lean`
- **Generator**: `scripts/gen_hiatus.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/Hiatus/{Paper}.json` → `{Paper}.lean`

### Word order samples

A paper's classification of its language sample: dominant clause order, adposition
type, noun–dependent orders, and the further per-language properties the paper records,
plus its table of order types with the languages attesting each (Greenberg 1963,
Appendices I and II, with the properties of the text and footnotes).

- **Schema**: `Linglib/Data/WordOrder/Schema.lean`
- **Generator**: `scripts/gen_word_order.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/WordOrder/{Paper}.json` → `{Paper}.lean`

### Corpus word-order data

The word-order data a paper draws from corpora: per-language counts of the two relative
orders of subject and object, per-language printed statistics of that order (its entropy and
the mutual information between case marking and syntactic role), and individually annotated
clauses recording the order of object and verb with text type, object length, and animacy.

- **Schema**: `Linglib/Data/WordOrder/Corpus/Schema.lean`
- **Generator**: `scripts/gen_word_order_corpus.py` (`--check` verifies sync)
- **Input/Output**: `Linglib/Data/WordOrder/Corpus/{Paper}.json` → `{Paper}.lean`

### PHOIBLE 2.0

- **Source**: [PHOIBLE Online](https://phoible.org/) (Moran & McCloy 2019)
- **Format**: Single CSV (~23 MB, 105K rows)
- **License**: CC BY-SA 3.0
- **Citation**: Moran, Steven & McCloy, Daniel (eds.) 2019. *PHOIBLE 2.0*. Jena: Max Planck Institute for the Science of Human History. <http://phoible.org>. DOI: 10.5281/zenodo.2626687
- **Download**: <https://github.com/phoible/dev/blob/master/data/phoible.csv> (`PHOIBLE/raw/phoible.csv`)
- **Generator**: `scripts/gen_phoible.py`
- **Output**: `Linglib/Data/PHOIBLE/Inventories/{Lang}.lean`, and `Linglib/Data/PHOIBLE/Chart.lean`, the feature matrix of each glyph. A glyph has the same feature values in every PHOIBLE inventory, so the chart is language-independent; it leaves out tones and the glyphs with contour values such as `-,+`.
- **Coverage**: 21 languages (Akan, Arabic, English, Finnish, French, Georgian, German, Hindi-Urdu, Hungarian, Japanese, Korean, Mandarin, Maori, Persian, Russian, Spanish, Swahili, Tagalog, Turkish, Yoruba, Zulu); the first inventory per ISO unless `ISO=ID` names another. A phoneme's feature matrix is its chart entry, written inline only for tones and contour-valued glyphs.

#### Regenerating

```bash
python3 scripts/gen_phoible.py            # default 16 ISOs
python3 scripts/gen_phoible.py jpn ces    # specific ISOs
python3 scripts/gen_phoible.py kor=2197   # a chosen inventory, by InventoryID
python3 scripts/gen_phoible.py --chart    # the glyph chart (`--chart --check` validates sync)
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
