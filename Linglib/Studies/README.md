# `Linglib/Studies/` — paper-anchored study files

Flat layout: one file per paper, named by author-year.

```
Linglib/Studies/{AuthorYear}.lean        -- namespace AuthorYear
```

For rare multi-file papers, a per-paper subdirectory:

```
Linglib/Studies/{AuthorYear}/Basic.lean      -- namespace AuthorYear
Linglib/Studies/{AuthorYear}/{Topic}.lean
```

The full set (current): `Beaver2001/`, `Charlow2021/`, `Heim1982/`,
`IppolitoKissWilliams2025/`, `OsborneGross2012/`, `StankovaSimik2024/`.

## Why flat?

Phenomenon taxonomy is editorial — many papers contribute to multiple
phenomena, and rename/merge/split decisions would force path churn. The
`@cite{key}` reverse index in `blog/data/references.bib` already provides
phenomenon-based discovery (and `grep -l "Phenomena.X" Studies/` recovers
ad-hoc groupings). Flat eliminates the placement debate.

## Cross-phenomenon name collisions

When the same paper appears in multiple phenomena (different chapters /
applications / aspects), suffix the *newer* arrival with a topical
descriptor, minimising churn to consumers of the existing file:

| Pattern | Example |
|---|---|
| Chapter suffix | `Cooper2023.lean` (Anaphora) + `Cooper2023Ch6.lean` (Modality) + `Cooper2023Ch7.lean` (Quantification) + `Cooper2023Ch8.lean` (Anaphora) |
| Phenomenon suffix | `Dryer2013.lean` (Complementation WALS) + `Dryer2013Question.lean` + `Dryer2013Negation.lean` |
| Topic suffix | `Heim1992Desire.lean` + `Heim1992Projection.lean` (same paper, two formalisations) |
| Suffix-on-arrival | `Rouillard2026.lean` (TenseAspect) + `Rouillard2026Gradability.lean` (the newer file gets the suffix) |

When two formalisations of the same paper define non-conflicting
identifiers and would naturally share `namespace AuthorYear`, they can
coexist as separate files extending the same namespace (this is how
`Heim1992Desire` and `Heim1992Projection` both keep `namespace Heim1992`
internally — Lean lets the namespace span files).

## Bridge files don't belong here

Files that synthesise across multiple papers but aren't anchored on a
single paper (e.g., `AspectualConsistency`, `TheoryComparison`,
`SPEDerivations`, `TowerDerivation`) belong in the relevant phenomenon
directory as topical siblings of the data files, or in `Theories/` if
they extend a framework (e.g., `Theories/Pragmatics/RelevanceTheory/Nonliteral.lean`).
Studies/ is paper-anchored content only.

## Examples and generated content

Per-paper example data is generated from `Linglib/Data/Examples/{AuthorYear}.json`
into a `namespace Examples ... end` block delimited by marker comments
(`-- BEGIN GENERATED EXAMPLES` / `-- END GENERATED EXAMPLES`) inside the
study file.

Generator: `python3 scripts/gen_examples.py <AuthorYear>` — searches
`Studies/AuthorYear.lean` and `Studies/AuthorYear/Basic.lean`.

Schema reference and format conventions:
[`Linglib/Data/Examples/README.md`](../Data/Examples/README.md). Leipzig
glossing rules per [Comrie/Haspelmath/Bickel 2008](https://www.eva.mpg.de/lingua/pdf/Glossing-Rules.pdf).
