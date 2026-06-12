import Linglib.Data.Generalizations.HomogeneityProjection
import Linglib.Data.Examples.KrizChemla2015

/-!
# [kriz-chemla-2015]: Trivalent truth-value judgments for embedded plurals

Empirical anchor for the homogeneity-projection literature. Križ & Chemla
(2015), "Two methods to find truth-value gaps and their application to the
projection problem of homogeneity," *Natural Language Semantics* 23(3):
205-248, introduce a binary-then-ternary truth-value judgment paradigm and
deploy it on plural definites embedded under quantifiers (`every`, `no`,
`exactly N`) plus sentential negation, across three experiment batches
(A1-A3 binary, B1-B3 ternary, C2-C4 ternary with grammatical
boys/presents stimuli).

## Main declarations

* `examples` — per-paper accessor (option B): K&C's contribution to the
  cross-paper projection pool, i.e. `KrizChemla2015.Examples.all`.

The encoded stimulus rows themselves live in the generated module
`Data.Examples.KrizChemla2015` (from
`Linglib/Data/Examples/KrizChemla2015.json` via `scripts/gen_examples.py`);
the pool at [[Generalizations.HomogeneityProjection]] imports them, and is where
cross-account testing of rival theories ([magri-2014],
[kriz-2016], [kriz-spector-2021], [bar-lev-2021]) lands.

## Implementation notes

The K&C examples live in the generated `Data.Examples.KrizChemla2015`
module; the projection hub imports them into its cross-paper test pool.
This file remains the paper-anchored entry point and narrative hub.

Three projector-synthesized fields are gone from the prior incarnation,
verified against the paper PDF:
- `Monotonicity` enum + `monotonicity` function — re-stipulated
  `Core.Logic.NaturalLogic.ContextPolarity` and contained a return-value /
  comment contradiction for `notEvery`.
- `ProjectionDatum`/`EmbeddedTruthConditions` structures with `Bool`
  predicate-shape fields and `String` informal-prose fields — violated
  CLAUDE.md's no-`Bool`-for-predicates and no-`String`-in-proof-relevant-code
  conventions; superseded by the typed `LinguisticExample` rows.
- Enum cases `exactlyOne` and `atLeastOne` — never tested in the paper.

A fourth correction was the `no` projection finding: the prior
encoding's `gapDetectable := false` reflected the A2/B2 null, but
[kriz-chemla-2015] §5.2.3 (Exp. C2) explicitly overturns it ("E-no
does show a gap, which, albeit small, is robust" — β=1.3 χ²=8.2 p=.004 on
Diag. 1, Table 9). The C2 finding lands as
`Examples.no_C2_gap` with `gap_detected = "true"`.

## Todo

* The presupposition account named by [kriz-chemla-2015]
  (Schwarzschild 1994 + [gajewski-2005]) has no linglib study file
  yet; adding one would close the three-rival theoretical landscape the
  paper discusses.
-/

namespace KrizChemla2015

open Data.Examples (LinguisticExample)

/--
Per-paper accessor: K&C 2015's stimulus rows (the generated
`Examples.all`), which the projection hub pools for cross-account
testing.
-/
def examples : List LinguisticExample := Examples.all

end KrizChemla2015
