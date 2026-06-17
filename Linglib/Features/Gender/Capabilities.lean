import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Gender.Basic

/-!
# HasGender — the gender-bearing capability
[corbett-1991]

The typeclass mixin for carriers that bear grammatical gender — the gender
axis of the capability tower over lexical carriers, the analogue of
`HasNumber` (`Features/Number/Capabilities.lean`) and `HasPerson`
(`Features/Person/Capabilities.lean`). A consumer (agreement checker,
resolution, semantics) requires `[HasGender α]` and works over any
representation: a UD feature bundle, a `Word`, a `Pronoun`.

The accessor is **label-valued** (`Option Gender`, the comparative-concept
vocabulary), because the mixin is the cross-linguistic interface:
language-particular fine-grained access goes through the language's
`Gender.System` carrier, not through this class. It is `Option`-valued
because underspecification is the typologically normal case: a carrier with
no gender marking is a wildcard for agreement, and most languages have no
gender at all ([corbett-1991]).

Instances live with their carriers (mathlib-style): `UD.MorphFeatures` here
(its type is upstream of this file); downstream carriers (`Word`, `Pronoun`)
declare theirs where they are defined.
-/

set_option autoImplicit false

/-- A carrier that bears grammatical gender. `none` = unmarked or
    underspecified (a wildcard for agreement, not a default value). -/
class HasGender (α : Type*) where
  /-- The comparative gender label the carrier bears. -/
  genderOf : α → Option Gender

/-- A UD morphology bundle bears the label its `gender` tag ingests
    (`Gender.fromUD`, total on UD genders). -/
instance : HasGender UD.MorphFeatures :=
  ⟨fun f => f.gender.map Gender.fromUD⟩

namespace HasGender

variable {α : Type*} {β : Type*} [HasGender α] [HasGender β]

/-- Gender compatibility between two (possibly heterogeneous) carriers:
    the slot values are compatible in the flat information order (`Compat`)
    — valued genders must coincide; an unvalued carrier is a wildcard.
    The gender axis of φ-agreement (`UD.MorphFeatures.compatible`). -/
abbrev Compatible (a : α) (b : β) : Prop :=
  Compat (α := Flat Gender) (genderOf a) (genderOf b)

theorem compatible_comm {a : α} {b : β} (h : Compatible a b) :
    Compatible b a :=
  h.symm

/-- An unvalued carrier is compatible with everything. -/
theorem compatible_of_none {a : α} (h : genderOf a = none) (b : β) :
    Compatible a b := by
  show Compat (α := Flat Gender) (genderOf a) (genderOf b)
  rw [h]; exact bot_compat _

end HasGender

/-- φ-compatibility entails gender compatibility: the `HasGender` mixin never
    diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`). -/
theorem UD.MorphFeatures.compatible_hasGender {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasGender.Compatible f1 f2 :=
  Features.compat_of_clause_map Gender.fromUD <| by
    unfold UD.MorphFeatures.compatible at h
    simp only [Bool.and_eq_true] at h
    tauto
