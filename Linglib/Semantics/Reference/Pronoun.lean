/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Presupposition.PhiFeatures
import Linglib.Semantics.Composition.Assignment

/-!
# The denotation of a pronoun

A `PersonalPronoun` entry denotes as a `Nominal` whose selector is the variable denotation
`interpPronoun`, the value of the entry's index under the assignment, and whose intrinsic
presupposition is the φ-feature presupposition of the resolved referent
(`PersonalPronoun.phiPresup`, `PersonalPronoun.denote`): the conjunction of the person, number
and gender presuppositions of `Presupposition.PhiFeatures`, read off the entry's referential
person and number and its gender. The selector does not vary with the world of evaluation
(`PersonalPronoun.isRigid_denote_selector`): a pronoun refers directly. This is the survey of
[buring-2012]: one denotation serves the bound, anaphoric and deictic uses, binding being an
operator on the assignment (`Composition/Binding.lean`), and an absent or unmarked feature
contributes the trivial presupposition, the treatment of [sauerland-2003].

## Implementation notes

The presupposition reads the entry's referential person and number
(`PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber`), not its agreement
features, so a polite pronoun that agrees as third plural presupposes its addressee
(`PersonalPronoun.phiPresup_congr`). The speaker, the addressee and the gender predicates are
parameters of the model, as the proximity predicates are for the demonstrative determiner.

## References

* [buring-2012]
* [sauerland-2003]
-/

open Presupposition Presupposition.PhiFeatures
open Reference

namespace PersonalPronoun

variable {E W : Type*} [PartialOrder E] (e : PersonalPronoun) (i : ℕ) (speaker addressee : E)
  (isFemale isInanimate : E → Prop)

/-- The φ-feature presupposition of a pronoun entry over an entity domain `E`: the person
presupposition of its referential person, the number presupposition of its referential number
and the gender presupposition of its gender, conjoined. The model supplies the speaker and the
addressee for person and the gender predicates; number atomicity comes from the parthood order. -/
def phiPresup : PartialProp E :=
  (personSem speaker addressee e.referentialPerson).and
    ((numberSem e.referentialNumber).and (genderSem isFemale isInanimate e.gender))

@[simp] theorem phiPresup_presup (x : E) :
    (e.phiPresup speaker addressee isFemale isInanimate).presup x ↔
      (personSem speaker addressee e.referentialPerson).presup x ∧
        (numberSem e.referentialNumber).presup x ∧
          (genderSem isFemale isInanimate e.gender).presup x :=
  Iff.rfl

/-- The φ-feature presupposition depends on the referential categories and the gender alone,
not on the agreement person and number. -/
theorem phiPresup_congr {e₁ e₂ : PersonalPronoun} (hr : e₁.referential = e₂.referential)
    (hg : e₁.gender = e₂.gender) :
    e₁.phiPresup speaker addressee isFemale isInanimate =
      e₂.phiPresup speaker addressee isFemale isInanimate := by
  simp only [phiPresup, referentialPerson, referentialNumber, hr, hg]

/-- A pronoun's denotation: the selector is the variable denotation `interpPronoun i`, always
defined under a total assignment, and the intrinsic presupposition is the φ-feature
presupposition of the resolved referent `g i`. -/
def denote : Nominal (Assignment E) W E where
  presup g _ := (e.phiPresup speaker addressee isFemale isInanimate).defined (g i)
  selector g _ := some (Semantics.Composition.interpPronoun i g)

@[simp] theorem denote_presup (g : Assignment E) (w : W) :
    (e.denote i speaker addressee isFemale isInanimate).presup g w =
      (e.phiPresup speaker addressee isFemale isInanimate).defined (g i) :=
  rfl

@[simp] theorem denote_selector (g : Assignment E) (w : W) :
    (e.denote i speaker addressee isFemale isInanimate).selector g w = some (g i) :=
  rfl

/-- A pronoun's referent does not vary with the world: the selector is rigid. -/
theorem isRigid_denote_selector (g : Assignment E) :
    IsRigid ((e.denote (W := W) i speaker addressee isFemale isInanimate).selector g) :=
  isRigid_const _

end PersonalPronoun
