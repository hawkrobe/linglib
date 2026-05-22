# `Linglib/Studies/` — paper-anchored study files

This is the migration target for paper-anchored studies that previously lived
at `Linglib/Phenomena/X/Studies/AuthorYear.lean`. New layout is **flat**:

```
Linglib/Studies/{AuthorYear}.lean
namespace {AuthorYear}
```

Multi-file papers (rare) use a per-paper subdirectory:

```
Linglib/Studies/{AuthorYear}/Basic.lean
Linglib/Studies/{AuthorYear}/{Topic}.lean
namespace {AuthorYear}     -- in Basic.lean (no path prefix)
```

## Why flat?

The previous plan grouped study files by phenomenon
(`Studies/{Phenomenon}/{AuthorYear}.lean`). Two reasons we moved away from
that:

1. **The phenomenon taxonomy is editorial.** Many papers contribute to
   multiple phenomena; a "primary phenomenon" tiebreaker rule existed
   precisely because the call is contested. Going flat eliminates the
   placement decision.
2. **`@cite{key}` already provides phenomenon-based discovery.** A reverse
   index from `bibkey` to consuming files (under `blog/data/references.bib`)
   recovers "show me all studies of X" without baking the categorisation
   into paths. Path churn (when phenomena get renamed/split/merged) is
   eliminated.

The cost is browsing affordance — `ls Studies/` lists files alphabetically
by author-year rather than grouped by topic. `grep -l "Phenomena.X" Studies/`
recovers the grouping when needed.

## Migration status (2026-05-22)

| Source location | Status |
|---|---|
| `Linglib/Studies/AuthorYear.lean` | **flat target** (canonical) |
| `Linglib/Phenomena/X/Studies/AuthorYear.lean` | **legacy** — migrate when touched |

Anaphora was the pilot batch (~30 single-file papers + the `Heim1982/`
subdirectory). The remaining ~75 phenomena still have studies under
`Linglib/Phenomena/X/Studies/`. New study files in unmigrated phenomena
should go directly under `Linglib/Studies/AuthorYear.lean` — no need to
land them in the old grouped path first.

## Cross-phenomenon imports

Studies can freely import from each other regardless of phenomenon. E.g.,
`Linglib/Phenomena/Agreement/Studies/PanchevaZubizarreta2018.lean` imports
`Linglib.Studies.CharnavelMateu2015` (an anaphora study) for its
binding-domain content.

## Examples and generated content

Per-paper example data is generated from `Linglib/Data/Examples/{AuthorYear}.json`
into a `namespace Examples ... end` block delimited by marker comments
(`-- BEGIN GENERATED EXAMPLES` / `-- END GENERATED EXAMPLES`) inside the
study file. JSON (not CSV) because the `LinguisticExample` schema has
nested fields (gloss pairs, alternatives, readings, source/reportedIn
objects) that don't fit cleanly in CSV.

The generator (`scripts/gen_examples.py`) searches both the flat target
(`Linglib/Studies/{AuthorYear}.lean`), the multi-file subdir form
(`Linglib/Studies/{AuthorYear}/Basic.lean`), and the legacy
`Linglib/Phenomena/*/Studies/{AuthorYear}.lean` path during the migration
window.

See [`Linglib/Data/Examples/README.md`](../Data/Examples/README.md) for
the schema reference, file-format conventions, and Leipzig glossing rules
([Comrie/Haspelmath/Bickel 2008](https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf)).
Generator: `scripts/gen_examples.py`. Schema: `Linglib/Data/Examples/Schema.lean`.
