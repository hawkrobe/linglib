import Linglib.Core.Logic.Trivalent
import Linglib.Features.Polarity
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.KrizChemla2015
import Linglib.Data.Examples.AghaJeretic2022
import Linglib.Data.Examples.Kriz2015

/-!
# Generalizations.HomogeneityGap — cross-paper prediction target

The homogeneity gap of unembedded plural definites (and their modal
analogues): a positive sentence is true in the ALL scenario, its negation
true in the NONE scenario, and in mixed (GAP) scenarios both are neither
clearly true nor clearly false. The generalisation predates any single
account ([lobner-2000], [kriz-2015], [kriz-chemla-2015],
[agha-jeretic-2022]); rival explanations include double strengthening
([magri-2014]), exhaustification ([bar-lev-2021]), and trivalent
supervaluation ([kriz-2016]).

Sibling of `Generalizations.HomogeneityProjection`, which covers the
*embedded* cells (operator × scenario); this file covers the unembedded
polarity × scenario grid. The `Predict` signatures differ (`Polarity` vs
`EmbeddingOperator` first argument), so the two pools stay separate.

## Main declarations

* `GapScenario` — ALL / NONE / GAP scenario triad.
* `GapPredict` — signature a rival account must implement:
  `Polarity → GapScenario → Trivalent`.
* `GapDatum` — typed empirical datum lifted from `LinguisticExample`
  rows by `fromExample` (paperFeatures keys `polarity`, `condition`,
  `gap_detected`; rows with an `embedding` key other than `unembedded`
  are excluded — those belong to the projection pool).
* `allData` — pooled rows from [kriz-chemla-2015] (unembedded
  baselines), [kriz-2015] (switches items), and [agha-jeretic-2022]
  (weak-necessity modal items).

Divergence theorems between rival accounts live in the comparing
paper's study file, not here.
-/

namespace Generalizations.HomogeneityGap

open Data.Examples (LinguisticExample SourceRef)
open Features (Polarity)

/-! ### Substrate -/

/--
Scenario triad for unembedded homogeneity items: all-positive baseline,
all-negative baseline, and the mixed scenario where the gap appears.
-/
inductive GapScenario where
  | all   -- every relevant individual has the property
  | none  -- no relevant individual has the property
  | gap   -- some but not all do (homogeneity violated)
  deriving Repr, DecidableEq

/-! ### Test-suite schema -/

/--
Prediction signature for accounts of the unembedded homogeneity gap:
given the sentence polarity and the scenario, the trivalent value the
account assigns.
-/
abbrev GapPredict := Polarity → GapScenario → Trivalent

/--
Empirical datum lifted from a paper-anchored `LinguisticExample`:
`observed` is the trivalent value the paper's judgments commit to in
this `(polarity, scenario)` cell.
-/
structure GapDatum where
  polarity : Polarity
  scenario : GapScenario
  observed : Trivalent
  source   : SourceRef
  deriving Repr, DecidableEq

/-! ### `LinguisticExample` adapter -/

/-- Read a `Polarity` from the `paperFeatures` `"polarity"` value. -/
def parsePolarity : String → Option Polarity
  | "positive" => some .positive
  | "negative" => some .negative
  | _          => none

/-- Read a `GapScenario` from the `paperFeatures` `"condition"` value. -/
def parseScenario : String → Option GapScenario
  | "ALL"  => some .all
  | "NONE" => some .none
  | "GAP"  => some .gap
  | _      => none

/--
Observed trivalent value for a baseline cell, determined by polarity:
a positive sentence is true in ALL and false in NONE; a negative one
the reverse.
-/
def baselineTruth (p : Polarity) (s : GapScenario) : Trivalent :=
  match p, s with
  | .positive, .all => .true
  | .negative, .all => .false
  | .positive, _    => .false
  | .negative, _    => .true

/--
Observed value for a GAP-scenario row. `.indet` when the paper detected
the gap (`gap_detected = "true"`); otherwise the row must assert its
bivalent judgment explicitly via a `classical_value` key (e.g. the
gap-free strong-necessity cells of [agha-jeretic-2022]). Gap rows with
neither key are not pool cells — they carry study-local refinements
(removers, borderline-response items, issue-relativized judgments) and
are excluded rather than assigned a fabricated value.
-/
def gapTruth (features : List (String × String)) : Option Trivalent :=
  if (features.lookup "gap_detected").getD "false" == "true" then
    some .indet
  else match features.lookup "classical_value" with
    | some "true"  => some .true
    | some "false" => some .false
    | _            => none

/--
Lift a `LinguisticExample` to a `GapDatum` via the `polarity`,
`condition`, `gap_detected`, and `classical_value` keys. Rows tagged
with an `embedding` key other than `"unembedded"` return `none` —
embedded cells belong to `Generalizations.HomogeneityProjection`.
-/
def fromExample (e : LinguisticExample) : Option GapDatum := do
  match e.paperFeatures.lookup "embedding" with
  | some emb => if emb != "unembedded" then none else pure ()
  | none     => pure ()
  let p ← parsePolarity (← e.paperFeatures.lookup "polarity")
  let s ← parseScenario (← e.paperFeatures.lookup "condition")
  let observed ← match s with
    | .gap => gapTruth e.paperFeatures
    | _    => some (baselineTruth p s)
  some { polarity := p, scenario := s, observed := observed,
         source := e.source }

/-! ### Pool -/

/--
Cross-paper pool of unembedded homogeneity-gap data. Rival accounts
pass their `GapPredict` implementations against this pool; per-datum
and divergence theorems live in the comparing papers' study files.
-/
def allData : List GapDatum :=
  (KrizChemla2015.Examples.all ++ AghaJeretic2022.Examples.all
    ++ Kriz2015.Examples.all).filterMap fromExample

end Generalizations.HomogeneityGap
