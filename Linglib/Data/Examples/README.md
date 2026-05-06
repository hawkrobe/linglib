# `Linglib/Data/Examples/` — typed linguistic example data

One JSON file per source paper (`Charlow2014.json`, `Hofmann2025.json`, ...)
co-located with the [`Schema.lean`](Schema.lean) they instantiate. Each
file is a top-level JSON array of example objects mirroring the
`LinguisticExample` Lean struct.

## Generator

```bash
python3 scripts/gen_examples.py <AuthorYear>
```

Reads `Linglib/Data/Examples/<AuthorYear>.json`, locates the unique study file
at `Linglib/Studies/*/<AuthorYear>.lean` (or
`Linglib/Phenomena/*/Studies/<AuthorYear>.lean` during the in-progress
top-level Studies migration), and replaces the marker-delimited block:

```lean
-- BEGIN GENERATED EXAMPLES
-- END GENERATED EXAMPLES
```

with a generated `namespace Examples ... end` section. Hand-edits between
the markers are silently overwritten on the next regeneration.

## Schema

See `Linglib/Data/Examples/Schema.lean` for the canonical type. Quick
field reference:

| Field | Type | Notes |
|---|---|---|
| `id` | string | `<authoryear>_<local>`, e.g. `"charlow2014_donkey1"` |
| `source` | `{bibkey, paperLabel}` | **originating** paper (e.g. `geach-1962` for the donkey) |
| `reportedIn` | `{bibkey, paperLabel}` or `null` | citing paper this CSV row sits under, when different from `source` |
| `language` | string (Glottocode) | e.g. `"stan1293"` for Standard English |
| `primaryText` | string | surface form (full discourse if multi-sentence) |
| `discourseSegments` | array of strings | empty `[]` for single-sentence; non-empty lists the utterances |
| `glossedTokens` | array of 2-string arrays | `[[surface, gloss], ...]`. Empty `[]` if no IGT (e.g., English-glossed-as-English) |
| `translation` | string | minimal English translation |
| `context` | string | scenario/discourse context where the judgment holds |
| `judgment` | one of `acceptable, marginal, questionable, unacceptable, ungrammatical` | sentence-level felicity |
| `alternatives` | array of `{form, judgment}` | within-example contrast pairs (e.g., Schwarz's `vom` vs `von dem`) |
| `readings` | array of `{name, judgment}` | multiple LFs / scope readings (e.g., donkey strong vs weak) |
| `comment` | string | analyst notes |
| `metaLanguage` | Glottocode | optional; default `"stan1293"` |
| `lgrConformance` | string | `""`, `"WORD_ALIGNED"`, or `"MORPHEME_ALIGNED"` |

## Leipzig glossing conventions

The `gloss` component of `glossedTokens` follows the **Leipzig Glossing Rules**:

> Comrie, B., Haspelmath, M., & Bickel, B. (2008). The Leipzig Glossing
> Rules: Conventions for interlinear morpheme-by-morpheme glosses.
> Department of Linguistics of the Max Planck Institute for Evolutionary
> Anthropology & the Department of Linguistics of the University of Leipzig.

Spec: <https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf>

Quick reference:
- `-` separates segmentable morphemes (affix boundaries)
- `.` separates two glosses corresponding to one form (fusion / portmanteau)
- `=` separates clitics from hosts
- SMALL CAPS for grammatical category labels (e.g., `INDEF`, `3SG`, `PST`,
  `NOM`, `REL`); plain lowercase for lexical glosses (`farmer`, `dog`)
- `1`/`2`/`3` for person; `SG`/`DU`/`PL` for number; gender
  (`M`/`F`/`N`) when relevant; case labels (`NOM`/`ACC`/`GEN`/...)
- Subscript indices for coreference (`Mary₁ ... her₁`) — not yet
  representable in the schema; `comment` field for now

## File-format style

Pretty-printed JSON, but **compact `glossedTokens`**: pack 3–4
`[surface, gloss]` pairs per line so the IGT alignment can be read at a
glance instead of scrolling through one-pair-per-line. Other arrays
(`discourseSegments`, `alternatives`, `readings`) get one element per line
for diff-friendliness — those entries are usually long strings or
structured objects.

```json
"glossedTokens": [
  ["Every", "every"], ["farmer", "farmer"], ["who", "REL.ANIM"],   ["owns", "own.PRS.3SG"],
  ["a",     "INDEF"], ["donkey", "donkey"], ["beats", "beat.PRS.3SG"], ["it",  "3SG.N"]
]
```

Whitespace in the JSON file does not affect generator output (the JSON is
parsed structurally).

## Provenance discipline

Hierarchical citation is the rule, not the exception. Most examples in
the literature are reported through later papers:

- Schwarz 2013 cites Ebert 1971a's Fering examples
- Charlow 2014 cites Geach 1962's donkey
- Hofmann 2025 cites Krahmer & Muskens 1995, Roberts 1989, Frank 1996

Convention: `source` is the **originating** paper (where the example was
first introduced or attested); `reportedIn` is the paper whose JSON file
this row sits in, when that paper is not the originator. For papers that
introduce their own examples, `reportedIn` is `null`.

## Bib entry requirement

Every `bibkey` (in both `source` and `reportedIn`) must resolve to an
entry in `blog/data/references.bib`. Per CLAUDE.md, fabrication is not
allowed — if a paper has no bib entry, add one (with verified DOI / title
/ journal / pages) before referencing the key.

## What this format does **not** yet support

The schema is consciously narrower than the literature it's eventually
aimed at. Known gaps:

- **Coreference indexing** (binder/bound subscripts) — Reinhart 1976,
  Fering Schwarz (8). Use `comment` field for now.
- **Tree-structured examples** where the bracketing IS the data
  (Bakay et al. 2026, syntactic minimal pairs).
- **Paradigm clusters** where N sentences only mean something together
  (Reinhart's (11a)–(11d)).
- **Paper-relativized classifications** (Schwarz's anaphoric / larger
  situation / bridging-producer / bridging-part-whole tags as typed
  fields rather than free-form `comment`).

Extensions land when a consuming study demands them.
