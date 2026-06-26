import Linglib.Features.Person.Basic
import Linglib.Features.Number.Basic
import Linglib.Features.Case.Basic

/-!
# Adjective Agreement Paradigms

Theory-neutral substrate for *which* φ/κ-features are morphologically realized on
adjectives in each syntactic position (predicative vs. attributive). This is the data
layer of the Modification Agreement Generalization ([alexeyenko-zeijlstra-2025]); the
theory-specific analysis (the Attr head, the direct-vs-mediated modification route)
lives in `Studies/AlexeyenkoZeijlstra2025.lean`.

Formerly `Syntax/Minimalist/Modification.lean`'s `MAGFeatureType`/`AdjAgreementEntry` —
relocated here so the per-language `Fragments/*/AdjAgreement.lean` files import
theory-neutral substrate rather than Minimalist theory.
-/

namespace Agreement

/-- An agreement feature realized on an adjective: a φ-feature (person/number/gender)
    or a κ-feature (case). -/
inductive AgrFeature where
  | person : Person → AgrFeature
  | number : Number → AgrFeature
  | gender : Nat → AgrFeature
  | kappa : Case → AgrFeature
  deriving DecidableEq, Repr

/-- An adjective agreement entry: the features morphologically realized on
    predicative vs. attributive adjectives, and all φ/κ-features available in the DP. -/
structure AdjAgreementEntry where
  /-- Features realized on predicative adjectives. -/
  predFeatures : List AgrFeature
  /-- Features realized on attributive adjectives. -/
  attrFeatures : List AgrFeature
  /-- All φ/κ-features available in the DP of this language. -/
  dpFeatures   : List AgrFeature
  deriving Repr

/-- Predicative and attributive adjectives realize the same agreement
    ([alexeyenko-zeijlstra-2025] MAG (34a), clause 1). -/
def AdjAgreementEntry.sameAgreement (e : AdjAgreementEntry) : Bool :=
  e.predFeatures.length == e.attrFeatures.length &&
  e.attrFeatures.all (e.predFeatures.contains ·)

/-- Attributive adjectives realize every DP φ/κ-feature
    ([alexeyenko-zeijlstra-2025] MAG (34a), clause 2). -/
def AdjAgreementEntry.phiKappaComplete (e : AdjAgreementEntry) : Bool :=
  e.dpFeatures.all (e.attrFeatures.contains ·)

end Agreement
