import Linglib.Studies.Krifka2007
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Data.Examples.AlexandropoulouGotzner2024a

/-!
# Alexandropoulou and Gotzner (2024a): relative and absolute adjectives under negation

Two rating experiments set Horn's face-based account of negative strengthening
against Krifka's complexity-based one on three kinds of negated antonym pairs:
weak relative (*not large* vs *not small*), weak absolute (*not clean* vs *not
dirty*) and strong (*not gigantic* vs *not tiny*, *not pristine* vs *not
filthy*). The accounts' applicability conditions differ — Horn needs a semantic
extension gap, Krifka's M-principle needs semantically equivalent competitors —
so the three cases pull them apart (the paper's Table 1).

The predictions are computed from the mechanisms over the four surface forms:
Horn's R-strengthening of the face-threatening negated positive and Q/R
middling of the double negative (`hornRanges`), Krifka's BiOT quadruplet from
`Krifka2007` (`krifkaRanges`), and its NACH extension as a comparison of
complexity deviations (`deviation`). The gap condition is read off the
Fragment's antonym classification. The reported findings — an asymmetry for
weak relatives only — confirm Horn on the weak cases, refute both Krifka
variants, and leave Horn's strong-adjective prediction unsupported.

## References

* [alexandropoulou-gotzner-2024a]
* [horn-1989]
* [krifka-2007b]
* [ruytenbeek-etal-2017]
-/

namespace AlexandropoulouGotzner2024a

open Degree (AntonymForm GradableAdjective InformationalStrength)
open Features (Asymmetry)
open Krifka2007 (Region krifkaQuadruplet)
open Data.Examples (LinguisticExample)
open English.Predicates.Adjectival (large small clean dirty gigantic tiny pristine filthy)

/-! ### Design cells -/

/-- Adjective type × informational strength; Table 1 pools the two strong cells. -/
inductive Cell
  | weakRelative
  | weakAbsolute
  | strongRelative
  | strongAbsolute
  deriving DecidableEq, Fintype

/-- The evaluatively positive and negative members of the cell's antonym pair. -/
def Cell.pair : Cell → GradableAdjective × GradableAdjective
  | .weakRelative   => (large, small)
  | .weakAbsolute   => (clean, dirty)
  | .strongRelative => (gigantic, tiny)
  | .strongAbsolute => (pristine, filthy)

/-- The design's strength factor. -/
def Cell.strength : Cell → InformationalStrength
  | .weakRelative | .weakAbsolute => .weak
  | _ => .strong

/-- The pair leaves a semantic extension gap: its antonyms are contrary. -/
def Cell.HasGap (c : Cell) : Prop := c.pair.1.antonymRelation = some .contrary

instance : DecidablePred Cell.HasGap :=
  λ c ↦ inferInstanceAs (Decidable (c.pair.1.antonymRelation = some .contrary))

/-- The relative/absolute split of the cells is the Fragment's derived Kennedy class. -/
theorem cell_classes :
    large.adjectiveClass = .relativeGradable ∧ gigantic.adjectiveClass = .relativeGradable ∧
    clean.adjectiveClass = .absoluteMaximum ∧ dirty.adjectiveClass = .absoluteMinimum ∧
    pristine.adjectiveClass = .absoluteMaximum ∧ filthy.adjectiveClass = .absoluteMinimum := by
  decide

/-- Only the weak absolute pair lacks a gap. -/
theorem hasGap_iff (c : Cell) : c.HasGap ↔ c ≠ .weakAbsolute := by
  cases c <;> decide

/-! ### Communicated ranges -/

/-- The scale regions each surface form may communicate. -/
abbrev Ranges := AntonymForm → Finset Region

/-- Positive and negative forms communicate mirror-image ranges. -/
def Ranges.Symmetric (r : Ranges) : Prop := ∀ f, r f.flip = (r f).image Region.flip

instance (r : Ranges) : Decidable r.Symmetric := Fintype.decidableForallFintype

def Ranges.asymmetry (r : Ranges) : Asymmetry :=
  if r.Symmetric then .symmetric else .asymmetric

/-- Horn's ranges, given a semantic gap: the negated positive is R-strengthened to
    the face-threatening antonym it conceals, while the prolix double negative is
    Q/R-restricted to the gap the simpler positive could not describe. -/
def hornRanges : Ranges
  | .positive    => {.positive}
  | .negative    => {.negative}
  | .notPositive => {.negative}
  | .notNegative => {.plateauLow, .plateauHigh}

/-- Krifka's ranges: the BiOT quadruplet of `Krifka2007`. -/
def krifkaRanges : Ranges := λ f ↦ (krifkaQuadruplet.filter (·.1 = f)).image (·.2)

theorem hornRanges_asymmetric : hornRanges.asymmetry = .asymmetric := by decide

theorem krifkaRanges_symmetric : krifkaRanges.asymmetry = .symmetric := by decide

/-! ### The Negative Adjectives Complexity Hypothesis -/

/-- Form complexity with (`true`) or without (`false`) NACH. Under NACH the negative
    adjective carries a covert negative morpheme, so *small* counts like *unhappy*;
    without it the simple antonyms are equally simple and their negations equally
    complex. -/
def complexity : Bool → AntonymForm → ℕ
  | true, f => f.complexity
  | false, .positive | false, .negative => 0
  | false, .notPositive | false, .notNegative => 3

/-- The simple form co-extensive with a form under bivalent semantics. -/
def simpleOf : AntonymForm → AntonymForm
  | .notPositive => .negative
  | .notNegative => .positive
  | f => f

/-- Excess complexity of a form over its co-extensive simple form — the amount of
    stereotype deviation the M-principle assigns it. -/
def deviation (nach : Bool) (f : AntonymForm) : ℕ :=
  complexity nach f - complexity nach (simpleOf f)

/-- Without NACH both negated forms deviate equally from their antonyms; with it
    *not small* deviates more from *large* than *not large* does from *small*. -/
theorem deviation_nach :
    deviation false .notPositive = deviation false .notNegative ∧
    deviation true .notPositive < deviation true .notNegative := by
  decide

/-! ### Table 1 -/

/-- Horn's prediction, where a semantic gap makes the account applicable. -/
def horn (c : Cell) : Option Asymmetry :=
  if c.HasGap then some hornRanges.asymmetry else none

/-- Krifka's prediction, with or without NACH: the M-principle needs semantically
    equivalent competitors, which only weak pairs provide (by bivalence for
    relatives, by entailment for absolutes). -/
def krifka (nach : Bool) (c : Cell) : Option Asymmetry :=
  match c.strength with
  | .strong => none
  | .weak =>
    some (if deviation nach .notPositive = deviation nach .notNegative then .symmetric
      else .asymmetric)

theorem table1_weakRelative :
    horn .weakRelative = some .asymmetric ∧ krifka false .weakRelative = some .symmetric ∧
    krifka true .weakRelative = some .asymmetric := by
  decide

theorem table1_weakAbsolute :
    horn .weakAbsolute = none ∧ krifka false .weakAbsolute = some .symmetric ∧
    krifka true .weakAbsolute = some .asymmetric := by
  decide

theorem table1_strong :
    ∀ c : Cell, c.strength = .strong →
      horn c = some .asymmetric ∧ krifka false c = none ∧ krifka true c = none := by
  decide

/-! ### Findings -/

/-- The reported interpretation patterns. Experiment 1 found a Negation effect for
    weak relatives (β = 0.64, p < .01) and none with strong as the reference level
    (p = 0.86); Experiment 2 found none for weak absolutes (p = 0.17) and only a
    marginal one for strong absolutes (p = 0.07). -/
def finding : Cell → Asymmetry
  | .weakRelative => .asymmetric
  | _ => .symmetric

/-- Horn is confirmed wherever it applies to a weak pair. -/
theorem horn_confirmed_on_weak :
    ∀ c : Cell, c.strength = .weak → ∀ p ∈ horn c, p = finding c := by
  decide

/-- Horn's asymmetry for strong pairs is not observed. -/
theorem horn_unsupported_on_strong :
    ∀ c : Cell, c.strength = .strong → horn c ≠ some (finding c) := by
  decide

/-- Krifka's original account fails on weak relatives, its NACH extension on weak
    absolutes. -/
theorem krifka_refuted :
    krifka false .weakRelative ≠ some (finding .weakRelative) ∧
    krifka true .weakAbsolute ≠ some (finding .weakAbsolute) := by
  decide

/-- A semantic extension gap is a precondition for negative strengthening. -/
theorem gap_precondition : ∀ c : Cell, finding c = .asymmetric → c.HasGap := by
  decide

/-! ### Rows -/

/-- Fragment entry for an adjective of the size and cleanliness items. -/
def entryOf : String → Option GradableAdjective
  | "large" => some large | "small" => some small
  | "gigantic" => some gigantic | "tiny" => some tiny
  | "clean" => some clean | "dirty" => some dirty
  | "pristine" => some pristine | "filthy" => some filthy
  | _ => none

/-- The surface form of a statement row, from its polarity and negation conditions. -/
def formOf (row : LinguisticExample) : Option AntonymForm :=
  match row.feature? "polarity", row.feature? "negation" with
  | some "positive", some "nonNegated" => some .positive
  | some "positive", some "negated" => some .notPositive
  | some "negative", some "nonNegated" => some .negative
  | some "negative", some "negated" => some .notNegative
  | _, _ => none

/-- A statement is in a negated condition exactly when it contains *not*. -/
theorem negated_iff_not :
    ∀ row ∈ Examples.all, ∀ n ∈ row.feature? "negation",
      (n = "negated" ↔ " not ".toList <:+: row.primaryText.toList) := by
  decide

end AlexandropoulouGotzner2024a
