import Linglib.Fragments.English.Pronouns
import Linglib.Semantics.Reference.PronounDenotation

/-!
# Büring 2012: pronouns

This file formalizes the semantics of definite pronouns in Büring's handbook survey, as theorems
about the project's pronoun denotation applied to the English Fragment's entries. A pronoun is
indexed and denotes the value its index has under the assignment; bound, anaphoric and deictic uses
share that one denotation, so a binder is an external operator manipulating the assignment rather
than a second lexical entry. The φ-features are presuppositions on the resolved referent: *she*
picks out the assignment value only when that value is a singular female, and is undefined —
neither true nor false, merely infelicitous — otherwise.

The unmarked feature values contribute nothing, so a pronoun that carries only unmarked values is
defined of any referent at all. That is the survey's underspecification treatment of *they*, whose
gender-neutrality is the absence of a gender feature rather than a feature of its own.

## Main results

* `selector_eq_assignment` — a pronoun denotes the assignment value at its index
* `undefined_of_non_female` — a feminine entry is undefined of a non-female referent
* `defined_of_unmarked_features` — an entry with only unmarked values imposes no condition
* `they_defined_where_she_undefined` — the two English entries at a male referent
* `bound_reading` — binding is an assignment update, with the entry's denotation unchanged

## References

* [buring-2012]
* [sauerland-2003]
-/

namespace Buring2012

open English.Pronouns (she they)
open Semantics.Composition (interpPronoun)
open Presupposition Presupposition.PhiFeatures

variable {E : Type} [PartialOrder E] (e : PersonalPronoun) (g : Assignment E) (i : ℕ)
  (spk adr : E) (isFemale isInanimate : E → Prop)

/-- A pronoun denotes the value of its index under the assignment: its selector is the canonical
variable lookup, the same one for the bound, anaphoric and deictic uses. -/
theorem selector_eq_assignment :
    (e.denote i spk adr isFemale isInanimate).selector g ⟨⟩
      = some (interpPronoun (E := E) (W := PUnit) i g) := rfl

/-- A feminine pronoun is undefined of a non-female referent: the feature does not assert that the
referent is female, it presupposes it, so the denotation has no value at all when it fails. -/
theorem undefined_of_non_female (scope : E → PUnit → Prop) (hfem : e.gender = some .feminine)
    (h : ¬ isFemale (g i)) :
    ¬ ((e.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ := by
  simp only [PersonalPronoun.denote, PersonalPronoun.phiPresup, hfem,
    Reference.NominalDenot.toPartialProp, PartialProp.and, femSem]
  exact fun hp => h hp.1.2.2

/-- *She* is undefined of a male referent. -/
theorem she_undefined_of_non_female (scope : E → PUnit → Prop) (h : ¬ isFemale (g i)) :
    ¬ ((she.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ :=
  undefined_of_non_female she g i spk adr isFemale isInanimate scope rfl h

/-- An entry carrying only unmarked values — third person, plural, no gender — presupposes nothing
of the referent, so it is defined wherever any pronoun is. Unmarked values are the absence of a
feature rather than a feature of their own, which is why the underspecified form can be used to
avoid a gender specification. -/
theorem defined_of_unmarked_features (scope : E → PUnit → Prop) (hp : e.person = some .third)
    (hn : e.number = some .plural) (hg : e.gender = none) :
    ((e.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ := by
  refine ⟨?_, rfl⟩
  simp only [PersonalPronoun.denote, PersonalPronoun.phiPresup, hp, hn, hg, PartialProp.and,
    thirdSem, plSem, PartialProp.top]
  exact ⟨trivial, trivial, trivial⟩

/-- *They* is defined of a referent of any gender. -/
theorem they_defined_regardless_of_gender (scope : E → PUnit → Prop) :
    ((they.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ :=
  defined_of_unmarked_features they g i spk adr isFemale isInanimate scope rfl rfl rfl

/-- The two entries come apart exactly at the referents the gender feature excludes: where *she*
has no value, *they* has one. -/
theorem they_defined_where_she_undefined (scope : E → PUnit → Prop) (h : ¬ isFemale (g i)) :
    ¬ ((she.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ ∧
      ((they.denote i spk adr isFemale isInanimate).toPartialProp scope g).presup ⟨⟩ :=
  ⟨she_undefined_of_non_female g i spk adr isFemale isInanimate scope h,
    they_defined_regardless_of_gender g i spk adr isFemale isInanimate scope⟩

/-- Binding leaves the pronoun alone: the binding operator updates the assignment at the pronoun's
index, and the unchanged denotation then returns the binder. There is no bound-pronoun lexeme. -/
theorem bound_reading (b : E) :
    (e.denote i spk adr isFemale isInanimate).selector (Function.update g i b) ⟨⟩ = some b := by
  simp only [PersonalPronoun.denote, interpPronoun, Function.update_self]

end Buring2012
