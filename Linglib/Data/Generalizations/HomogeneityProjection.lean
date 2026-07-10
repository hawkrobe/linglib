import Linglib.Core.Logic.Truth3
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.KrizChemla2015

/-!
# Generalizations.HomogeneityProjection — cross-paper prediction target

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
* `ProjectionPredict` — the shared signature any account of homogeneity
  projection must satisfy; given an `(operator, scenario)` pair, predict a
  trivalent `Truth3` value.
* `ProjectionDatum` — typed empirical datum; lifted from the raw
  `LinguisticExample` rows by `fromExample`.
* `Examples` (generator-managed) — pooled stimulus rows from each paper
  that contributes projection-relevant data; per-paper JSON inputs live in
  `Linglib/Data/Examples/<Paper>.json`, and this hub imports each paper's
  generated `Data.Examples.<Paper>` module (see `scripts/gen_examples.py`).
* `allData` — the test pool: every `LinguisticExample` whose
  `paperFeatures` carry the keys this hub recognises.

Studies files (e.g. [[KrizChemla2015]], [[AugurzkyEtAl2023]]) retrieve their
paper-specific slice from their own `<Paper>.Examples.all` (option-B
per-paper accessor pattern).

## Implementation notes

This file is the entry point for cross-account testing of homogeneity
projection. The shape is: a `ProjectionPredict` signature each account
implements; a `ProjectionDatum` carrying observed outcomes; decidable
theorems comparing each account's prediction to each datum, including
*divergence* theorems where two accounts disagree.

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

* Wire `ProjectionPredict` implementations from each rival account: the
  scalar-implicature/exhaustification accounts ([magri-2014],
  [bar-lev-2021]), the supervaluation/trivalence accounts
  ([spector-2013], [kriz-2016], [kriz-spector-2021]), and
  the presupposition account ([gajewski-2005] + Schwarzschild 1994 —
  no linglib study file yet).
* Prove decidable per-datum predictions and cross-account divergence
  theorems once those implementations land.
* Add a denotation hook `EmbeddingOperator → ∀ α, Quantification.GQ α`
  once accounts derive predictions structurally rather than dispatch on
  label (per [peters-westerstahl-2006] discipline).
-/

namespace Generalizations.HomogeneityProjection

open Trivalent (Truth3)
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
/ GAP triad; `gapQ` and `gapQQ` are the `exactly N` refinements that
isolate the at-least-reading from genuine homogeneity projection.
-/
inductive GapScenario where
  | trueScenario   -- all-positive baseline
  | falseScenario  -- all-negative baseline
  | gap            -- standard mixed scenario (homogeneity violated)
  | gapQ           -- at-least reading possible (exactly-only)
  | gapQQ          -- at-least reading ruled out (exactly-only)
  deriving Repr, DecidableEq

/-! ### Test-suite schema -/

/--
Theoretical-prediction signature any account of homogeneity projection
must satisfy: given an embedder label and a scenario, predict the
trivalent `Truth3` value the account commits to.
-/
abbrev ProjectionPredict := EmbeddingOperator → GapScenario → Truth3

/--
Empirical datum derived from a paper-anchored `LinguisticExample`.
`observed` is the trivalent value the paper's findings commit to in this
`(operator, scenario)` cell; `source` is the originating paper.
-/
structure ProjectionDatum where
  operator : EmbeddingOperator
  scenario : GapScenario
  observed : Truth3
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
Compute the observed `Truth3` value for a `(scenario, gapDetected)` cell.

Baseline conditions are unambiguous: `TRUE → .true`, `FALSE → .false`.
For gap-bearing scenarios, gap detection means the empirical distribution
peaks on the trivalent middle (`.indet`); a non-detection on a
gap-bearing scenario means an alternative reading (typically an at-least
reading for non-monotonic embedders) rendered the sentence non-gappy.
-/
def observedTruth (scenario : GapScenario) (gapDetected : Bool) : Truth3 :=
  match scenario, gapDetected with
  | .trueScenario,  _    => .true
  | .falseScenario, _    => .false
  | _,              true => .indet
  | _,              false => .true

/--
Lift a `LinguisticExample` to a `ProjectionDatum`, reading the
`operator`, `condition`, and `gap_detected` keys from `paperFeatures`.
Returns `none` for rows whose `paperFeatures` lack the recognised tags —
those rows are not part of this hub's pool.
-/
def fromExample (e : LinguisticExample) : Option ProjectionDatum :=
  match e.paperFeatures.lookup "operator", e.paperFeatures.lookup "condition" with
  | some opStr, some condStr =>
    match parseOperator opStr, parseScenario condStr with
    | some op, some sc =>
      let gapDetected := (e.paperFeatures.lookup "gap_detected").getD "false" == "true"
      some { operator := op, scenario := sc,
             observed := observedTruth sc gapDetected,
             source := e.source }
    | _, _ => none
  | _, _ => none

/-! ### Pool -/

/--
Cross-paper pool of projection-relevant data, derived from the imported
per-paper `Examples.all` lists by `fromExample`. Each entry carries its
originating `SourceRef` for provenance. Rival theories of projection
should pass their `ProjectionPredict` implementations against this pool.
-/
def allData : List ProjectionDatum :=
  KrizChemla2015.Examples.all.filterMap fromExample

end Generalizations.HomogeneityProjection
