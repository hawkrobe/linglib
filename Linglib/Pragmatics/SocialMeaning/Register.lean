import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Register

This file defines the register of a linguistic form. A register is a way of speaking that a
speech community ties to a kind of situation, and variation in register is variation within
one speaker across situations rather than between speakers. The formality of the situation is
the dimension recorded here: a form belongs to careful or written language, to casual speech,
or to neither. English *must* and *perhaps* are formal beside *have to* and *maybe*, the German
simple past is the narrative tense of writing, and Indonesian *telah* is the written
counterpart of *sudah*.

Register is a property of the form and of the situation of use. The social relation a form
presents between the speaker and a person it refers to or addresses is a separate property,
its honorific level, `SocialMeaning.HonorificLevel`. The Korean speech-style particles carry
one value of each: the polite and the formal particle present the same relation to the
addressee and differ in the formality of the discourse.

## Main definitions

* `SocialMeaning.Register`: the informal, neutral and formal registers, linearly ordered by
  formality.

## References

* [S. Rotter and M. Liu, *A Register Approach to Modal (Non-)Concord in English: An
  Experimental Study of Linguistic and Social Meaning* (2025)][rotter-liu-2025]
* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

namespace SocialMeaning

/-- The register of a form is the formality of the situations in which speakers use it. -/
inductive Register where
  /-- Colloquial, casual speech: *have to*, *maybe*. -/
  | informal
  /-- Unmarked for formality. -/
  | neutral
  /-- Written, literary or careful language: *must*, *shall*, *perhaps*. -/
  | formal
  deriving DecidableEq, Fintype, Repr

namespace Register

/-- Registers are ordered by formality, `informal < neutral < formal`. -/
instance : LinearOrder Register :=
  LinearOrder.lift' Register.ctorIdx fun a b h ↦ by cases a <;> cases b <;> first | rfl | cases h

instance : BoundedOrder Register where
  top := formal
  le_top := by decide
  bot := informal
  bot_le := by decide

end Register

end SocialMeaning
