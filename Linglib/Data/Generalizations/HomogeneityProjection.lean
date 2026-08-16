import Linglib.Core.Data.Trivalent
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.KrizChemla2015
import Linglib.Data.Generalizations.HomogeneityGap

/-!
# Generalizations.HomogeneityProjection — cross-paper data pool

Cross-paper test substrate for how the homogeneity gap of plural definites
projects under embedding quantifiers and operators. The pattern's empirical
literature spans [lobner-2000], [gajewski-2005],
[spector-2013], [magri-2014], [kriz-chemla-2015],
[kriz-2016], [bar-lev-2021], [augurzky-etal-2023],
[kriz-spector-2021], and [haslinger-2025-diss]; the empirical
generalisation predates any one formal account, justifying a theory-neutral
`Data/Generalizations/` anchor.

## Main declarations

* `EmbeddingOperator` — operator labels recurring across the literature.
* `GapScenario` — scenario classification used by the C-series experiments
  (TRUE / FALSE / GAP / GAP? / GAP??).
* `ProjectionDatum` — typed empirical datum; lifted from the raw
  `LinguisticExample` rows by `fromExample`.
* `Examples` (generator-managed) — pooled stimulus rows from each paper
  that contributes projection-relevant data; per-paper JSON inputs live in
  `Linglib/Data/Examples/<Paper>.json`, and this hub imports each paper's
  generated `Data.Examples.<Paper>` module (see `scripts/gen_examples.py`).
* `allData` — the test pool: every `LinguisticExample` whose
  `paperFeatures` carry the keys this hub recognises.

## Implementation notes

This file is the data side of cross-account testing of homogeneity
projection: a `ProjectionDatum` per observed outcome, pooled in `allData`.
Accounts state their predictions in their own study files, at the
granularity their paper supports, and are run against the pool there —
restricted by `source.bibkey` to papers available at each study's
publication date. Decidable per-datum and divergence theorems live in
those study files too.

The substrate is restricted to the smallest set of operator cases that
closes the current ≥2-consumer graduation criterion: `every` / `no`
(every major contribution tests these), `exactlyTwo` (introduced by
[kriz-chemla-2015] Exps. A3/B3/C3/C4), and `notEvery` (the
no/notEvery asymmetry from [augurzky-etal-2023]). Extend as new
consumers land.

There is deliberately *no* projector-stipulated `monotonicity :
EmbeddingOperator → ContextPolarity` function — the classical mapping
(`notEvery ↦ downward` by De Morgan) disagrees with the empirical
observation that `notEvery` patterns with `every` rather than `no` in
QUD-manipulation acceptance ([augurzky-etal-2023]), so any single
mapping would be wrong for at least one consumer.

## Todo

* Run the rival accounts postdating [kriz-chemla-2015] against this
  pool: the exhaustification account ([bar-lev-2021]) and the mature
  supervaluation/trivalence accounts ([kriz-2016], [kriz-spector-2021]).
  The account variants the paper itself assesses — [magri-2014]-style
  implicature construals, [spector-2013] supervaluation, and
  [schwarzschild-1994] / [lobner-2000] / [gajewski-2005] presupposition
  with universal projection — are already run against it in
  `Studies/KrizChemla2015.lean`, restricted to the paper's tested cells.
* Pool a second paper's rows (JSON-ify the [augurzky-etal-2023]
  acceptance data) to close the ≥ 2-papers admission prong.
* Add a denotation hook `EmbeddingOperator → ∀ α, Quantification.GQ α`
  once accounts derive predictions structurally rather than dispatch on
  label (per [peters-westerstahl-2006] discipline).
-/

namespace Generalizations.HomogeneityProjection

open Data.Examples (LinguisticExample SourceRef)

/-! ### Substrate -/

/--
Quantifier-operator labels for plural-definite embedding environments,
restricted to operators actually consumed by linglib's homogeneity-
projection study files.
-/
inductive EmbeddingOperator where
  | every
  | no
  | exactlyTwo
  | notEvery
  deriving Repr, DecidableEq

/--
Scenario classification used by the trivalent-judgment paradigm
([kriz-chemla-2015]). The first three are the canonical TRUE / FALSE
/ GAP triad; `gapQ` and `gapQQ` are the `exactly N` refinements probing
the two ways the some-substituted and all-substituted variants of the
sentence can pattern in a candidate gap situation (Table 12's s5/s6).
-/
inductive GapScenario where
  | trueScenario   -- clear-truth baseline
  | falseScenario  -- clear-falsity baseline
  | gap            -- some-variant true, all-variant false (homogeneity violated)
  | gapQ           -- some-variant and all-variant both false (exactly-only)
  | gapQQ          -- some-variant false, all-variant true (exactly-only)
  deriving Repr, DecidableEq

/-! ### Datum schema -/

/--
Empirical datum derived from a paper-anchored `LinguisticExample`.
`observed` is the trivalent value the paper's findings commit to in this
`(operator, scenario)` cell; `source` is the originating paper.
-/
structure ProjectionDatum where
  operator : EmbeddingOperator
  scenario : GapScenario
  observed : Trivalent
  source   : SourceRef
  deriving Repr, DecidableEq

/-! ### `LinguisticExample` adapter -/

/--
Read an `EmbeddingOperator` from a string value of the `paperFeatures`
`"operator"` key. `none` for unrecognised labels.
-/
def parseOperator : String → Option EmbeddingOperator
  | "every"      => some .every
  | "no"         => some .no
  | "exactlyTwo" => some .exactlyTwo
  | "notEvery"   => some .notEvery
  | _            => none

/--
Read a `GapScenario` from a string value of the `paperFeatures`
`"condition"` key. `none` for unrecognised labels.
-/
def parseScenario : String → Option GapScenario
  | "TRUE"  => some .trueScenario
  | "FALSE" => some .falseScenario
  | "GAP"   => some .gap
  | "GAP?"  => some .gapQ
  | "GAP??" => some .gapQQ
  | _       => none

/--
Lift a `LinguisticExample` to a `ProjectionDatum`, reading the
`operator`, `condition`, `gap_detected`, and `classical_value` keys from
`paperFeatures`. Baseline conditions are unambiguous (`TRUE → .true`,
`FALSE → .false`); gap-family rows resolve via
`HomogeneityGap.gapTruth`: `.indet` when the paper detected the gap,
otherwise the bivalent value the row asserts through `classical_value`
(e.g. the gap? cells of [kriz-chemla-2015] Exp. C3, judged completely
false). Rows lacking the recognised tags are not part of this hub's pool.
-/
def fromExample (e : LinguisticExample) : Option ProjectionDatum := do
  let op ← parseOperator (← e.paperFeatures.lookup "operator")
  let sc ← parseScenario (← e.paperFeatures.lookup "condition")
  let observed ← match sc with
    | .trueScenario  => some .true
    | .falseScenario => some .false
    | _              => HomogeneityGap.gapTruth e.paperFeatures
  some { operator := op, scenario := sc, observed := observed,
         source := e.source }

/-! ### Pool -/

/--
Cross-paper pool of projection-relevant data, derived from the imported
per-paper `Examples.all` lists by `fromExample`. Each entry carries its
originating `SourceRef` for provenance. Rival theories of projection are
run against this pool in the study files.
-/
def allData : List ProjectionDatum :=
  KrizChemla2015.Examples.all.filterMap fromExample

end Generalizations.HomogeneityProjection
