import Linglib.Semantics.Degree.Adjective
import Linglib.Semantics.Degree.Boundedness
import Linglib.Data.Examples.Sassoon2013

/-!
# Sassoon (2013): A Typology of Multidimensional Adjectives

This file formalizes the paper's corpus typology of multidimensional adjectives. A
multidimensional adjective binds its dimensions with an implicit quantifier, and exception
phrases reveal its force: *healthy except for high blood pressure* operates on a universal over
dimensions, so an adjective is conjunctive when dimensional exception phrases occur with it in
positive contexts, disjunctive when they occur under negation, and mixed when both occur
alike. The paper's criterion classifies an adjective from the frequencies of dimensional uses
in the two contexts, conjunctive or disjunctive when one is at least three times the other
(`classify`), and applied to its sample it yields the paper's three lists (`typology`). Two
predictors are tested. Antonym polarity: under a negation theory of antonymy the negative
member of a pair is the negation of the positive one, so De Morgan turns a universal over
dimensions into an existential, the substrate's `deMorgan_conjunctive_disjunctive`; the
clearly conjunctive adjectives are all judged positive and the clearly disjunctive ones
negative (`polarity_predicts_binding`), and within an antonym pair the two are never both
clearly bound the same way (`antonyms_negate`). Standard type: total adjectives should be
conjunctive and partial ones disjunctive, the mechanism being the substrate's
`predictedBinding`; by the inference tests no total adjective is disjunctive, but partial
adjectives include conjunctive ones, so the biconditional fails and the paper reports only a
correlation with modifier-based totality (`total_not_disjunctive`,
`partial_conjunctive_exists`). Comparatives inherit the binding of their base except that
*worse* is milder than *bad* (`comparatives_inherit`).

## Implementation notes

The rows carry the paper's tables: the percentages of dimensional uses in positive and
negated contexts, the polarity means in hundredths, the normalized totality index and the
inference-test standard type. The correlations the paper reports between polarity and
normalized conjunctivity and between totality and conjunctivity are not formalized. The
`MultidimAdj` record with a scale-structure field and its `hypothesis3Holds` test are kept for
`Studies/Tham2025.lean`, which builds entries in it.

## References

* [sassoon-2013]
* [kennedy-mcnally-2005]
* [heim-2006]
* [buring-2007]
-/

namespace Sassoon2013

open Degree Data.Examples

/-- The paper's criterion: an adjective is conjunctive when its dimensional uses in positive
contexts are at least three times those in negated contexts, disjunctive in the converse case,
and mixed otherwise. -/
def classify (conj disj : ℕ) : DimensionBindingType :=
  if 3 * disj ≤ conj then .conjunctive else if 3 * conj ≤ disj then .disjunctive else .mixed

/-- A sampled adjective's binding type from its corpus percentages. -/
def binding? (x : LinguisticExample) : Option DimensionBindingType :=
  (x.nat? "conj").bind λ c => (x.nat? "disj").map (classify c)

/-- The row of an adjective. -/
def rowOf (form : String) : Option LinguisticExample :=
  Examples.all.find? (·.primaryText == form)

/-- The criterion applied to the sample yields the paper's lists: the conjunctive adjectives,
the disjunctive ones, and the mixed remainder. -/
theorem typology :
    ∀ x ∈ Examples.all, ∀ b ∈ binding? x,
      (b = .conjunctive ↔
          x.primaryText ∈ ["normal", "typical", "healthy", "familiar", "healthier"]) ∧
        (b = .disjunctive ↔
          x.primaryText ∈ ["bad", "sick", "atypical", "abnormal", "different"]) := by
  decide +kernel

/-! ### Antonym polarity -/

/-- The polarity judgments confirm the a priori classification: the positive adjectives are
judged above the midpoint of the scale and the negative ones below it. -/
theorem polarity_judgments :
    ∀ x ∈ Examples.all, ∀ p ∈ x.nat? "polarity",
      (x.feature? "positive" = some "true" ↔ 400 < p) := by
  decide +kernel

/-- The clearly conjunctive adjectives are all judged positive and the clearly disjunctive
ones negative. -/
theorem polarity_predicts_binding :
    ∀ x ∈ Examples.all, ∀ b ∈ binding? x, ∀ p ∈ x.nat? "polarity",
      (b = .conjunctive → 400 < p) ∧ (b = .disjunctive → p < 400) := by
  decide +kernel

/-- Within an antonym pair, whenever both members are clearly bound, the negative member's
binding is the De Morgan dual of the positive member's. -/
theorem antonyms_negate :
    ∀ x ∈ Examples.all, ∀ a ∈ x.feature? "antonym", ∀ y ∈ rowOf a,
      ∀ b ∈ binding? x, ∀ b' ∈ binding? y, b ≠ .mixed → b' ≠ .mixed → b' = b.negate := by
  decide +kernel

/-! ### Standard type -/

/-- The paper's standard types by the inference tests, as positive standards. -/
private def standards : List (String × PositiveStandard) :=
  [("total", .maxEndpoint), ("partial", .minEndpoint), ("relative", .contextual)]

/-- No total adjective is disjunctive, as the standard-type hypothesis predicts. -/
theorem total_not_disjunctive :
    ∀ x ∈ Examples.all, ∀ s ∈ x.parse? "standard" standards, ∀ b ∈ binding? x,
      s = .maxEndpoint → b ≠ .disjunctive := by
  decide +kernel

/-- A partial adjective can be conjunctive, against the standard-type hypothesis: *familiar*
and the comparative *healthier* are partial by the inference tests yet clearly conjunctive. -/
theorem partial_conjunctive_exists :
    ∃ x ∈ Examples.all, x.parse? "standard" standards = some .minEndpoint ∧
      binding? x = some .conjunctive ∧ predictedBinding .minEndpoint ≠ .conjunctive := by
  decide +kernel

/-! ### Comparatives -/

/-- A comparative inherits the binding of its base unless the base is clearly disjunctive:
*healthier* is conjunctive like *healthy* and *better* mixed like *good*, while *worse* is
mixed although *bad* is disjunctive, the pair whose difference the paper finds significant. -/
theorem comparatives_inherit :
    ∀ x ∈ Examples.all, ∀ f ∈ x.feature? "base", ∀ y ∈ rowOf f,
      (binding? y ≠ some .disjunctive → binding? x = binding? y) ∧
        (binding? y = some .disjunctive → binding? x = some .mixed) := by
  decide +kernel

/-! ### The record used across papers -/

/-- An adjective classified by evaluative polarity, scale structure and binding type. -/
structure MultidimAdj where
  form : String
  isPositive : Bool
  scaleType : Boundedness
  binding : DimensionBindingType
  deriving Repr, DecidableEq

/-- The binding the standard-type hypothesis predicts from a scale structure's default
standard. -/
def predictedFromStandard (b : Boundedness) : DimensionBindingType :=
  predictedBinding b.defaultStandard

/-- Whether an adjective's binding is the one its scale structure predicts. -/
def hypothesis3Holds (a : MultidimAdj) : Bool :=
  a.binding == predictedFromStandard a.scaleType

end Sassoon2013
