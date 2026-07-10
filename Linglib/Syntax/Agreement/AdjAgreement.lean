import Linglib.Features.Person.Basic
import Linglib.Features.Number.Basic
import Linglib.Features.Gender.Basic
import Linglib.Features.Case.Basic

/-!
# Adjective Agreement Paradigms

Theory-neutral substrate for *which* φ/κ-features are morphologically realized on
adjectives in each syntactic position (predicative vs. attributive). This is the data
layer of the Modifier-Noun Adjacency Generalization ([alexeyenko-zeijlstra-2025]); the
theory-specific analysis (the Attr head, the direct-vs-mediated modification route)
lives in `Studies/AlexeyenkoZeijlstra2025.lean`.

## Main declarations

- `Agreement.FeatureSpec`: the φ/κ-features a form is specified for, one `Finset`
  per feature dimension
- `Agreement.AdjAgreementEntry`: the specifications of predicative and attributive
  adjectives, plus all features available in the DP
- `Agreement.AdjAgreementEntry.SameAgreement`, `.PhiKappaComplete`: the two clauses
  of MAG condition (34a)
-/

namespace Agreement

/-- The φ/κ-features a form is specified for: one `Finset` per feature dimension
    (φ = person/number/gender, κ = case). Unmentioned dimensions default to `∅`. -/
structure FeatureSpec where
  persons : Finset Person := ∅
  numbers : Finset Number := ∅
  genders : Finset Gender := ∅
  cases   : Finset Case := ∅
  deriving DecidableEq

namespace FeatureSpec

/-- Pointwise inclusion: every feature `a` is specified for, `b` is too. -/
instance : LE FeatureSpec where
  le a b := a.persons ⊆ b.persons ∧ a.numbers ⊆ b.numbers ∧
            a.genders ⊆ b.genders ∧ a.cases ⊆ b.cases

instance : DecidableLE FeatureSpec :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

end FeatureSpec

/-- An adjective agreement entry: the features morphologically realized on
    predicative vs. attributive adjectives, and all φ/κ-features available in the DP. -/
structure AdjAgreementEntry where
  /-- Features realized on predicative adjectives. -/
  predFeatures : FeatureSpec
  /-- Features realized on attributive adjectives. -/
  attrFeatures : FeatureSpec
  /-- All φ/κ-features available in the DP of this language. -/
  dpFeatures   : FeatureSpec
  deriving DecidableEq

namespace AdjAgreementEntry

variable (e : AdjAgreementEntry)

/-- Predicative and attributive adjectives realize the same agreement
    ([alexeyenko-zeijlstra-2025] MAG (34a), clause 1). -/
def SameAgreement : Prop := e.predFeatures = e.attrFeatures

/-- Attributive adjectives realize every DP φ/κ-feature
    ([alexeyenko-zeijlstra-2025] MAG (34a), clause 2). -/
def PhiKappaComplete : Prop := e.dpFeatures ≤ e.attrFeatures

instance : Decidable e.SameAgreement := inferInstanceAs (Decidable (_ = _))

instance : Decidable e.PhiKappaComplete := inferInstanceAs (Decidable (_ ≤ _))

end AdjAgreementEntry

end Agreement
