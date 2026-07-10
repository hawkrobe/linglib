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

- `Agreement.AgrFeature`: a φ-feature (person/number/gender) or κ-feature (case)
  realized on an adjective
- `Agreement.AdjAgreementEntry`: the feature sets realized on predicative vs.
  attributive adjectives, plus all features available in the DP
- `Agreement.AdjAgreementEntry.SameAgreement`, `.PhiKappaComplete`: the two clauses
  of MAG condition (34a)
-/

namespace Agreement

/-- An agreement feature realized on an adjective: a φ-feature (person/number/gender)
    or a κ-feature (case). -/
inductive AgrFeature where
  | person : Person → AgrFeature
  | number : Number → AgrFeature
  | gender : Gender → AgrFeature
  | kappa : Case → AgrFeature
  deriving DecidableEq, Repr

/-- An adjective agreement entry: the features morphologically realized on
    predicative vs. attributive adjectives, and all φ/κ-features available in the DP. -/
structure AdjAgreementEntry where
  /-- Features realized on predicative adjectives. -/
  predFeatures : Finset AgrFeature
  /-- Features realized on attributive adjectives. -/
  attrFeatures : Finset AgrFeature
  /-- All φ/κ-features available in the DP of this language. -/
  dpFeatures   : Finset AgrFeature
  deriving DecidableEq

namespace AdjAgreementEntry

variable (e : AdjAgreementEntry)

/-- Predicative and attributive adjectives realize the same agreement
    ([alexeyenko-zeijlstra-2025] MAG (34a), clause 1). -/
def SameAgreement : Prop := e.predFeatures = e.attrFeatures

/-- Attributive adjectives realize every DP φ/κ-feature
    ([alexeyenko-zeijlstra-2025] MAG (34a), clause 2). -/
def PhiKappaComplete : Prop := e.dpFeatures ⊆ e.attrFeatures

instance : Decidable e.SameAgreement := inferInstanceAs (Decidable (_ = _))

instance : Decidable e.PhiKappaComplete := inferInstanceAs (Decidable (_ ⊆ _))

end AdjAgreementEntry

end Agreement
