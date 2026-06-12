import Linglib.Data.Examples.TieuEtAl2020
import Linglib.Features.Polarity
import Linglib.Semantics.Alternatives.Lexical

/-!
# Tieu, Bill, Romoli & Crain (2020) [tieu-etal-2020]

Testing theories of plural meanings. *Cognition* 205, 104307.

Three experiments comparing adults' and children's interpretations of
bare plurals in upward- and downward-entailing environments. The results
support an implicature approach to multiplicity inferences: children
compute fewer multiplicity inferences than adults, in parallel with their
behavior on standard scalar implicatures, and the two inference types
are correlated within children.

## Core Argument

The paper adjudicates between three theories of why "Emily fed giraffes"
means "more than one":

1. **Ambiguity** ([farkas-de-swart-2010]): plural is polysemous
   (inclusive/exclusive), Strongest Meaning Hypothesis selects the
   stronger reading.
2. **Implicature** ([sauerland-2003], [spector-2007], [zweig-2009]):
   plural literally means "one or more," the "more than one" inference
   is a scalar implicature with the singular as alternative.
3. **Homogeneity** ([kriz-2015]): multiplicity arises from homogeneity
   presupposition.

Key discriminating prediction (Uniformity Prediction): if multiplicity
inferences are scalar implicatures, children should compute fewer of both,
and rates should be correlated.

## Main declarations

* `PluralTheory` — the paper's three-way theory taxonomy, with
  `usesSIMechanism` as the discriminating mechanistic property.
* `stimulus?` — row lookup over the generated `Examples.all` pool
  (`Data/Examples/TieuEtAl2020.json`).
* `implicature_uniquely_supported` — only the implicature theory derives
  multiplicity via the SI mechanism.
* `multiplicity_parallels_si_de_blocking` — the multiplicity pattern
  matches the DE blocking of classical scalar implicatures.
-/

namespace TieuEtAl2020

open Alternatives.Number (NumberExpr numberScale)
open Data.Examples (LinguisticExample)


-- ### Competing theories

/-- The paper's three-way taxonomy of theories of the multiplicity
    inference: ambiguity ([farkas-de-swart-2010]), implicature
    ([sauerland-2003], [spector-2007], [zweig-2009]), homogeneity
    ([kriz-2015]). -/
inductive PluralTheory where
  /-- Plural is ambiguous; Strongest Meaning Hypothesis resolves. -/
  | ambiguity
  /-- Plural literally means "one or more"; multiplicity is implicature. -/
  | implicature
  /-- Plural interpretation via homogeneity presupposition. -/
  | homogeneity
  deriving DecidableEq, Repr, Inhabited

/-- Does the theory analyze multiplicity as arising via the same mechanism
    as scalar implicatures? The paper's discriminating predictions —
    acquisition delay, within-child SI correlation, polarity asymmetry,
    singular-context truth-value asymmetry — all transfer from known SI
    properties via this property. -/
def PluralTheory.usesSIMechanism : PluralTheory → Bool
  | .implicature => true
  | _ => false

/-- The implicature theory is uniquely identified by the SI mechanism,
    hence by any of the predictions that transfer through it. -/
theorem implicature_uniquely_supported :
    ∀ t : PluralTheory, t.usesSIMechanism = true → t = .implicature := by
  intro t h
  cases t <;> simp_all [PluralTheory.usesSIMechanism]


-- ### Stimuli

/-- Look up a stimulus row in the paper's example pool by `id`. -/
def stimulus? (id : String) : Option LinguisticExample :=
  Examples.all.find? (·.id == id)

/-- Core multiplicity datum, positive form: "Emily fed giraffes". -/
abbrev fedGiraffesPos : Option LinguisticExample :=
  stimulus? "tieuetal2020_fed_giraffes_pos"

/-- Core multiplicity datum, negative form: "Emily didn't feed giraffes". -/
abbrev fedGiraffesNeg : Option LinguisticExample :=
  stimulus? "tieuetal2020_fed_giraffes_neg"

/-- Experiment 1, upward-entailing TVJ trial: "Emily fed pigs" after a
    story in which she fed exactly one pig (rejection indicates
    computing multiplicity). -/
abbrev exp1_positive : Option LinguisticExample :=
  stimulus? "tieuetal2020_exp1_positive"

/-- Experiment 1, downward-entailing TVJ trial: "Emily didn't feed
    giraffes" after she fed exactly one (acceptance indicates a local
    multiplicity reading under negation). -/
abbrev exp1_negative : Option LinguisticExample :=
  stimulus? "tieuetal2020_exp1_negative"

/-- Experiment 3, positive plural in a singular context: "Koala bought
    pears" when Koala bought exactly one pear. -/
abbrev exp3_positive_plural : Option LinguisticExample :=
  stimulus? "tieuetal2020_exp3_positive_plural"

/-- Experiment 3, negative plural in a singular context: "Koala didn't
    buy pears" when Koala bought exactly one pear. -/
abbrev exp3_negative_plural : Option LinguisticExample :=
  stimulus? "tieuetal2020_exp3_negative_plural"

/-- The core monotonicity pattern: the multiplicity reading is available
    in the positive datum but unavailable under negation. -/
theorem consistent_with_monotonicity_data :
    fedGiraffesPos.bind (·.readings.lookup "multiplicity (>1)") =
      some .acceptable ∧
    fedGiraffesNeg.bind (·.readings.lookup "multiplicity (>1)") =
      some .unacceptable := by
  decide

/-- Experiment 1 reading availability: the multiplicity reading is fully
    available in the UE trial; the local multiplicity reading under
    negation is only marginal (adults' negative-condition rate was
    moderate). -/
theorem exp1_multiplicity_reading_contrast :
    exp1_positive.bind (·.readings.lookup "multiplicity (>1)") =
      some .acceptable ∧
    exp1_negative.bind
      (·.readings.lookup "multiplicity (>1) local under negation") =
      some .marginal := by
  decide


-- ### Experimental results

/-- Inference rate for a group in a condition. -/
structure InferenceRate where
  /-- Which group -/
  group : String
  /-- Inference type -/
  inferenceType : String
  /-- Polarity of context -/
  polarity : Features.Polarity
  /-- Rate of inference-consistent responses (qualitative) -/
  rate : String
  deriving Repr

/-- Experiment 1 key results (qualitative — no exact numbers cited). -/
def exp1Results : List InferenceRate :=
  [ { group := "Adults", inferenceType := "multiplicity"
    , polarity := .positive, rate := "high" }
  , { group := "Adults", inferenceType := "multiplicity"
    , polarity := .negative, rate := "moderate" }
  , { group := "Children", inferenceType := "multiplicity"
    , polarity := .positive, rate := "low" }
  , { group := "Children", inferenceType := "multiplicity"
    , polarity := .negative, rate := "low" }
  ]

/-- Experiment 2 key results (qualitative). -/
def exp2Results : List InferenceRate :=
  [ { group := "Adults", inferenceType := "multiplicity"
    , polarity := .positive, rate := "high" }
  , { group := "Children", inferenceType := "multiplicity"
    , polarity := .positive, rate := "low" }
  , { group := "Adults", inferenceType := "scalar (some)"
    , polarity := .positive, rate := "high" }
  , { group := "Children", inferenceType := "scalar (some)"
    , polarity := .positive, rate := "low" }
  ]


-- ### Uniformity Prediction

/--
The Uniformity Prediction: if multiplicity inferences are scalar
implicatures, then the between-group pattern (children < adults)
should be the same for both inference types.

The paper confirms this prediction and additionally finds that
children's rates on the two types are significantly correlated.
-/
structure UniformityResult where
  /-- Do children compute fewer multiplicity inferences than adults? -/
  childrenFewerMultiplicity : Bool
  /-- Do children compute fewer scalar implicatures than adults? -/
  childrenFewerSI : Bool
  /-- Are the two rates correlated within children? -/
  correlatedInChildren : Bool
  deriving Repr

def uniformityConfirmed : UniformityResult :=
  { childrenFewerMultiplicity := true
  , childrenFewerSI := true
  , correlatedInChildren := true
  }

/-- All three components of the Uniformity Prediction are confirmed. -/
theorem uniformity_all_confirmed :
    uniformityConfirmed.childrenFewerMultiplicity = true ∧
    uniformityConfirmed.childrenFewerSI = true ∧
    uniformityConfirmed.correlatedInChildren = true :=
  ⟨rfl, rfl, rfl⟩


-- ### Connection to Horn scale infrastructure

/-- The singular/plural scale predicts multiplicity as a scalar implicature:
    using the plural (weaker) implicates the negation of the singular (stronger). -/
theorem plural_has_singular_alternative :
    Alternatives.strongerAlternatives numberScale .plural = [.singular] := by
  decide

/-- In DE contexts, the scale reverses (weaker alternatives are relevant),
    so the multiplicity inference does not arise. -/
theorem de_context_no_multiplicity :
    Alternatives.scalarAlternativesInContext numberScale .plural .downward = [] := by
  decide

/-- In UE contexts, the singular is the relevant alternative,
    producing the multiplicity inference. -/
theorem ue_context_multiplicity :
    Alternatives.scalarAlternativesInContext numberScale .plural .upward = [.singular] := by
  decide


-- ### Experiment 3: singular contexts (adults-only, ternary judgment)

/-!
Experiment 3 uses a ternary judgment task (small/medium/large strawberry
for false/neither/true) with adults on Amazon Mechanical Turk.

In singular contexts (exactly one object acted upon), only the SI
mechanism predicts a positive/negative truth-value asymmetry: "Koala
bought pears" is literally true with a false implicature (misleading),
while "Koala didn't buy pears" is literally false. On lexical or
presuppositional accounts both have the same status. Together with
`implicature_uniquely_supported`, the observed asymmetry singles out
`PluralTheory.implicature`.
-/

/-- Adults assign different reward status to positive vs negative plurals
    in singular contexts: intermediate reward for the (literally true but
    misleading) positive, minimal for the (literally false) negative. -/
theorem exp3_confirms_asymmetry :
    exp3_positive_plural.bind (·.paperFeatures.lookup "preferred_reward") =
      some "intermediate" ∧
    exp3_negative_plural.bind (·.paperFeatures.lookup "preferred_reward") =
      some "minimal" := by
  decide


-- ### Multiplicity parallels scalar implicatures

/-- The multiplicity inference exhibits DE blocking: available in the
    positive fed-giraffes row, unavailable under negation — the same
    UE-arises / DE-blocked pattern as the classical *some*/*all* scalar
    implicature ([horn-1972]). -/
theorem multiplicity_parallels_si_de_blocking :
    fedGiraffesPos.bind (·.readings.lookup "multiplicity (>1)") =
      some .acceptable ∧
    fedGiraffesNeg.bind (·.readings.lookup "multiplicity (>1)") =
      some .unacceptable :=
  ⟨by decide, by decide⟩

/-- Both the number scale and the quantifier scale predict the same
    pattern: stronger alternatives in UE, none/weaker in DE. -/
theorem scales_predict_same_pattern :
    (Alternatives.scalarAlternativesInContext numberScale .plural .upward).length > 0 ∧
    (Alternatives.scalarAlternativesInContext numberScale .plural .downward).length = 0 ∧
    (Alternatives.scalarAlternativesInContext
      Alternatives.Quantifiers.quantScale .some_ .upward).length > 0 := by
  decide

end TieuEtAl2020
