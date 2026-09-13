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

A `PersonalPronoun` entry denotes as a `NominalDenot` whose selector is the variable denotation
`interpPronoun`, the value of the entry's index under the assignment, and whose intrinsic
presupposition is the φ-feature presupposition read off the entry's person, number and gender
through the cells of `Presupposition.PhiFeatures` (`PersonalPronoun.phiPresup`,
`PersonalPronoun.denote`). This is the survey of [buring-2012]: one denotation serves the
bound, anaphoric and deictic uses, binding being an operator on the assignment
(`Composition/Binding.lean`), and an absent or unmarked feature contributes the trivial
presupposition, the treatment of [sauerland-2003].

## Implementation notes

Number values beyond singular and plural and the non-sex-based genders contribute the trivial
cell; the bridges `Number.fromUD` and `Gender.Features.fromGender` are the principled route,
deferred until a study needs them.

## References

* [buring-2012]
* [sauerland-2003]
-/

open Presupposition Presupposition.PhiFeatures
open Reference (NominalDenot)
open Semantics.Composition (interpPronoun)

/-- The conjoined φ-feature presupposition of a pronoun entry over an entity domain `E`: the
model supplies the speaker and addressee for person and the gender predicates; number
atomicity comes from the parthood order. An absent or uncovered feature contributes
`PartialProp.top`. -/
def PersonalPronoun.phiPresup {E : Type*} [PartialOrder E] (e : PersonalPronoun)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) : PartialProp E :=
  PartialProp.and
    (match e.person with
      | some .first  => firstSem speaker
      | some .second => secondSem speaker addressee
      | some .third  => thirdSem
      | _            => PartialProp.top)
    (PartialProp.and
      (match e.number with
        | some .singular => sgSem E
        | some .plural => plSem E
        | _          => PartialProp.top)
      (match e.gender with
        | some .feminine  => femSem isFemale
        | some .neuter    => neutSem isInanimate
        | some .masculine => mascSem
        | _               => PartialProp.top))

/-- A pronoun's denotation: the selector is the variable denotation `interpPronoun i`, always
defined under a total assignment, and the intrinsic presupposition is the φ-feature
presupposition of the resolved referent `g i`. The static case, with a trivial world. -/
def PersonalPronoun.denote {E : Type} [PartialOrder E] (e : PersonalPronoun) (i : ℕ)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) :
    NominalDenot (Assignment E) PUnit E where
  presup := λ g _ => (e.phiPresup speaker addressee isFemale isInanimate).presup (g i)
  selector := λ g _ => some (interpPronoun (E := E) (W := PUnit) i g)
