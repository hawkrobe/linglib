import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Syntax.Phi.Gender.Basic

/-!
# The gender-bearing capability

This file defines the class of carriers that bear a comparative gender label, and the
agreement relation it induces.

A carrier bears a gender label or none, the bottom of the flat information order, which is
the typologically normal case since most languages have no gender at all. Two carriers are
compatible when their labels coincide or one is unvalued; language-particular access to a
system's own genders goes through `Gender.System` instead.

## Main definitions

* `HasGender`: a carrier of a comparative gender label.
* `HasGender.Compatible`: slot compatibility of two carriers' labels in the flat order.

## References

* [corbett-1991]
-/

/-- A carrier of grammatical gender. `⊥` = the carrier does not mark
gender. -/
class HasGender (α : Type*) where
  /-- The comparative gender label the carrier bears, if marked. -/
  genderOf : α → Flat Gender

export HasGender (genderOf)

/-- A UD bundle bears the label its `gender` tag ingests (`Gender.fromUD`,
total on UD genders). -/
instance : HasGender UD.MorphFeatures :=
  ⟨λ f => f.gender.map Gender.fromUD⟩

instance : HasGender Gender := ⟨(↑·)⟩

/-- Gender compatibility: valued genders coincide, an unvalued carrier is a
wildcard. -/
abbrev HasGender.Compatible {α β : Type*} [HasGender α] [HasGender β]
    (a : α) (b : β) : Prop :=
  Compat (genderOf a) (genderOf b)

/-- φ-compatibility of UD bundles entails gender compatibility. -/
theorem UD.MorphFeatures.compatible_hasGender {f₁ f₂ : UD.MorphFeatures}
    (h : f₁.compatible f₂ = true) :
    HasGender.Compatible f₁ f₂ :=
  Features.compat_of_clause_map Gender.fromUD (UD.MorphFeatures.compatible_gender h)
