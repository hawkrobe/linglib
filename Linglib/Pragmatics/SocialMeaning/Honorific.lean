import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Honorific levels

This file defines the honorific level of a linguistic form. An honorific level is the social
relation a form presents between the speaker and a person, the referent of a pronoun or the
addressee of an allocutive marker. Magahi grades the second person in three levels,
nonhonorific *tõ*, honorific *tũ* and high honorific *apne*, and its verbal suffixes mark the
level of the subject and that of the addressee. A binary system, the familiar and polite
pronouns of German, Italian or Tamil, uses the lower two levels.

The level is relational. In the analysis Alok and Bhalla review, the honorific feature of a
nominal orders the speaker against its referent: the nonhonorific level presents the speaker
as at least the referent's equal, the honorific level as below the referent, and the high
honorific level as far below. Each nominal of a clause sets its own level, so a level belongs
to a form and not to an utterance. It is independent of the form's register,
`SocialMeaning.Register`, which records the formality of the situation of use.

## Main definitions

* `SocialMeaning.HonorificLevel`: the nonhonorific, honorific and high honorific levels,
  linearly ordered by the deference they present.

## References

* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

namespace SocialMeaning

/-- The honorific level of a form is the relation it presents between the speaker and the person
it refers to or addresses. -/
inductive HonorificLevel where
  /-- The speaker is at least the person's equal: Magahi *tõ*, German *du*. -/
  | nonhonorific
  /-- The speaker is below the person: Magahi *tũ*, German *Sie*. -/
  | honorific
  /-- The speaker is far below the person: Magahi *apne*. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

namespace HonorificLevel

/-- Honorific levels are ordered by deference, `nonhonorific < honorific < highHonorific`. -/
instance : LinearOrder HonorificLevel :=
  LinearOrder.lift' HonorificLevel.ctorIdx fun a b h ↦ by
    cases a <;> cases b <;> first | rfl | cases h

instance : BoundedOrder HonorificLevel where
  top := highHonorific
  le_top := by decide
  bot := nonhonorific
  bot_le := by decide

end HonorificLevel

end SocialMeaning
