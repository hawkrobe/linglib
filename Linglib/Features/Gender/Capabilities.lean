/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Gender.Basic

/-!
# The gender-bearing capability

`HasGender` equips a carrier with the comparative gender label it bears;
`HasGender.Compatible` is the induced agreement relation, slot compatibility
in the flat information order. The label vocabulary is the cross-linguistic
interface; language-particular fine-grained access goes through the language's
`Gender.System`. `⊥` is the typologically normal case: most languages have no
gender at all ([corbett-1991]).
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
  ⟨fun f => f.gender.map Gender.fromUD⟩

instance : HasGender Gender := ⟨(↑·)⟩

/-- Gender compatibility: valued genders coincide, an unvalued carrier is a
wildcard. -/
abbrev HasGender.Compatible {α β : Type*} [HasGender α] [HasGender β]
    (a : α) (b : β) : Prop :=
  Compat (genderOf a) (genderOf b)

/-- φ-compatibility of UD bundles entails gender compatibility. -/
theorem UD.MorphFeatures.compatible_hasGender {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasGender.Compatible f1 f2 :=
  Features.compat_of_clause_map Gender.fromUD (UD.MorphFeatures.compatible_gender h)
