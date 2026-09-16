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
presupposition is that the resolved referent lies in the entry's φ-domain
(`PersonalPronoun.phiDom`, `PersonalPronoun.denote`), the intersection of `Person.dom` at the
context of utterance, `Number.dom` and `Gender.dom` at the entry's referential person and number
and its gender. The selector does not vary with the world of evaluation
(`PersonalPronoun.isRigid_denote_selector`): a pronoun refers directly. This is the survey of
[buring-2012]: one denotation serves the bound, anaphoric and deictic uses, binding being an
operator on the assignment (`Composition/Binding.lean`), and an absent or unmarked feature
restricts nothing, the treatment of [sauerland-2003].

## Implementation notes

The φ-domain reads the entry's referential person and number
(`PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber`), not its agreement
features, so a polite pronoun that agrees as third plural presupposes its addressee
(`PersonalPronoun.phiDom_congr`). The speaker and the addressee are the agent and the addressee
of the context of utterance (`Reference.Context`), and the female and the inanimate referents
are the natural gender the entity domain comes equipped with (`NaturalGender`).

## References

* [buring-2012]
* [sauerland-2003]
-/

open Reference

namespace PersonalPronoun

variable {E W P T : Type*} [PartialOrder E] [NaturalGender E] (e : PersonalPronoun) (i : ℕ)
  (c : Context W E P T)

/-- The φ-domain of a pronoun entry over an entity domain `E`: the person domain of its
referential person at the context of utterance, the number domain of its referential number and
the gender domain of its gender, intersected. -/
def phiDom : Set E :=
  Person.dom c e.referentialPerson ∩
    Number.dom e.referentialNumber ∩
    Gender.dom e.gender

@[simp] theorem mem_phiDom (x : E) :
    x ∈ e.phiDom c ↔
      x ∈ Person.dom c e.referentialPerson ∧ x ∈ Number.dom e.referentialNumber ∧
        x ∈ Gender.dom e.gender := by
  simp only [phiDom, Set.mem_inter_iff, and_assoc]

/-- The φ-domain depends on the referential categories and the gender alone, not on the
agreement person and number. -/
theorem phiDom_congr {e₁ e₂ : PersonalPronoun} (hr : e₁.referential = e₂.referential)
    (hg : e₁.gender = e₂.gender) : e₁.phiDom c = e₂.phiDom c := by
  simp only [phiDom, referentialPerson, referentialNumber, hr, hg]

/-- A pronoun's denotation: the selector is the variable denotation `interpPronoun i`, always
defined under a total assignment, and the intrinsic presupposition is that the resolved referent
`g i` lies in the φ-domain. -/
def denote : Nominal (Assignment E) W E where
  presup g _ := g i ∈ e.phiDom c
  selector g _ := some (Semantics.Composition.interpPronoun i g)

@[simp] theorem denote_presup (g : Assignment E) (w : W) :
    (e.denote i c).presup g w = (g i ∈ e.phiDom c) :=
  rfl

@[simp] theorem denote_selector (g : Assignment E) (w : W) :
    (e.denote i c).selector g w = some (g i) :=
  rfl

/-- A pronoun's referent does not vary with the world: the selector is rigid. -/
theorem isRigid_denote_selector (g : Assignment E) :
    IsRigid ((e.denote i c).selector g) :=
  isRigid_const _

end PersonalPronoun
