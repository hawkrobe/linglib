# `Linglib/Studies/` — paper-anchored study files

This is the migration target for paper-anchored studies that previously lived
at `Linglib/Phenomena/X/Studies/AuthorYear.lean`. New layout:

```
Linglib/Studies/{Phenomenon}/{AuthorYear}.lean
namespace Studies.{Phenomenon}.{AuthorYear}
```

## Migration status (2026-05-05)

| Phenomenon | Status | Notes |
|---|---|---|
| `Anaphora/` | **migrated** | Pilot batch — 30 files + `Heim1982/` subdir |
| (everything else) | **not migrated** | Still at `Linglib/Phenomena/X/Studies/` |

**For new contributors:** if you're adding a study to a phenomenon that
hasn't migrated yet, put it under `Linglib/Phenomena/{X}/Studies/` with the
old `Phenomena.{X}.Studies.{AuthorYear}` namespace. When that phenomenon
migrates as a batch, the relocation script will rename uniformly.

For phenomena that *have* migrated (currently only Anaphora), put new study
files under `Linglib/Studies/{Phenomenon}/` with the new namespace.

## Why migrate?

Per `CLAUDE.md` — anchoring discipline says paper-anchored content lives in a
single, predictable place keyed by the paper, not by editorial decisions
about which phenomenon "owns" it. The top-level layout makes this uniform:
`Studies/{Phenomenon}/{AuthorYear}.lean` mirrors how a working linguist
thinks ("Charlow 2014 on anaphora" → `Studies/Anaphora/Charlow2014.lean`)
rather than burying the studies inside a deeper hierarchy.

## Cross-phenomenon imports

Migrated studies can freely import from un-migrated phenomena's studies (and
vice versa) — the namespace just differs. E.g.,
`Linglib/Phenomena/Agreement/Studies/PanchevaZubizarreta2018.lean` already
imports `Linglib.Studies.Anaphora.CharnavelMateu2015` across the
phenomenon-migration boundary. Lean doesn't care about co-location.

## Examples and generated content

Per-paper example data is generated from `Linglib/Data/Examples/{AuthorYear}.json`
into a `namespace Examples ... end` block delimited by marker comments
(`-- BEGIN GENERATED EXAMPLES` / `-- END GENERATED EXAMPLES`) inside the
study file. JSON (not CSV) because the `LinguisticExample` schema has
nested fields (gloss pairs, alternatives, readings, source/reportedIn
objects) that don't fit cleanly in CSV.

See [`Linglib/Data/Examples/README.md`](../Data/Examples/README.md) for
the schema reference, file-format conventions, and Leipzig glossing rules
([Comrie/Haspelmath/Bickel 2008](https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf)).
Generator: `scripts/gen_examples.py`. Schema: `Linglib/Data/Examples/Schema.lean`.
