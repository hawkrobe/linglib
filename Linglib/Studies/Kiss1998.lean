/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Interval.Set.Basic
import Linglib.Semantics.Alternatives.Basic
import Linglib.Semantics.Exhaustification.Excluder
import Linglib.Semantics.Focus.Interpretation

/-!
# É. Kiss (1998): Identificational Focus versus Information Focus

This file formalizes [kiss-1998]'s distinction between identificational focus, which in
Hungarian moves to the immediately preverbal position and expresses exhaustive identification,
and information focus, which stays in situ after the verb and merely marks its content as new.
The two types differ in interpretation (`FocusType.interpret`): identificational focus
exhaustifies the prejacent over the alternatives evoked by the contextually given set, the
`Exhaustification.exh` of [chierchia-2006], and information focus is the bare prejacent.
The paper's characterisation of exhaustive identification, that the focus "is identified as
the exhaustive subset of this set for which the predicate phrase actually holds", is the
theorem `exh_Ici`, and the coordination test and the dialogue test by which the paper
diagnoses exhaustivity come out as theorems on the hat-and-coat scenario of its examples
(`szabolcsi_test`, `farkas_test`). The distributional restrictions of §3 follow from the same
semantics, exhaustive identification being "exclusion by identification": a universal
quantifier identifies without excluding (`exh_Ici_restrictor`), a *some*-phrase excludes
without identifying (`exh_nonempty_eq_empty`), and an additive *also* or *even* phrase
contradicts its own presupposition unless the alternatives have been narrowed by a prior
identification, the paper's (18) (`disjoint_exh_additive`, `additive_exh_of_notMem`).

## Implementation notes

* The scenario tracks only which of the given elements the predicate phrase holds of, so a
  world is a subset of the given set, the proposition that the predicate holds of a group
  `s` is the principal upper set `Set.Ici s`, and exhaustive identification over the given
  set `A` is the interval `Set.Icc s (s ∪ Aᶜ)`: exactly `s` among the given elements, with
  the non-given ones unconstrained.
* *csak* 'only' phrases are obligatorily identificational because *csak* assigns the
  identificational focus feature (§8); the exclusion is the position's and *csak* adds an
  evaluative presupposition, which is outside this model.

## TODO

* §4 scope, §5.2 the cleft as the English realisation of identificational focus, §7 focus
  iteration and projection, and §9 the [+exhaustive] and [+contrastive] parametrisation
  across Italian, Romanian, Catalan, Greek, Arabic and Finnish.

## References

* [kiss-1998]
* [chierchia-2006]
-/

namespace Kiss1998

open Exhaustification Focus.Interpretation Set

variable {ι : Type*} {A : Set ι} {a b : ι}

/-- The alternatives a focused constituent evokes over the contextually given set `A`: for
each given element, that the predicate phrase holds of it. -/
def alternatives (A : Set ι) : PropFocusValue (Set ι) := (λ i => Ici {i}) '' A

/-- The alternatives are those Hamblin composition assigns to the predicate phrase applied to
a focused argument ranging over the given set. -/
theorem alternatives_eq (A : Set ι) (a : ι) :
    alternatives A = ((λ i => Ici {i}) <$> (⟨a, A⟩ : WithAlternatives ι)).alternatives := by
  ext q
  simp only [alternatives, mem_image, WithAlternatives.mem_alternatives_map]

/-- The two focus types: identificational focus, which in Hungarian sits immediately before
the verb, and information focus, which stays in situ after it. -/
inductive FocusType
  | identificational
  | information
  deriving DecidableEq, Repr

/-- The interpretation of a focus type over the given set `A`: identificational focus
exhaustifies its prejacent over the alternatives, information focus asserts it as is. -/
def FocusType.interpret (A : Set ι) : FocusType → Set (Set ι) → Set (Set ι)
  | .identificational => exh (alternatives A)
  | .information => id

@[simp] theorem interpret_identificational (p : Set (Set ι)) :
    FocusType.identificational.interpret A p = exh (alternatives A) p := rfl

@[simp] theorem interpret_information (p : Set (Set ι)) :
    FocusType.information.interpret A p = p := rfl

/-! ### Exhaustive identification (§2) -/

/-- Exhaustive identification of a group over the given set, the paper's (9): the predicate
holds of `s`, and of no other given element. -/
theorem exh_Ici (A s : Set ι) : exh (alternatives A) (Ici s) = Icc s (s ∪ Aᶜ) := by
  ext w
  simp only [mem_exh, alternatives, mem_Ici, mem_Icc, forall_mem_image, Ici_subset_Ici,
    singleton_subset_iff]
  refine and_congr_right λ _ => ⟨λ h i hiw => ?_, λ h i hiA hiw => ?_⟩
  · exact (mem_union _ _ _).2 ((em (i ∈ A)).imp_left (h · hiw))
  · exact ((mem_union _ _ _).1 (h hiw)).resolve_right (not_not.2 hiA)

/-- Over the whole domain, exhaustive identification of `s` says that the predicate holds of
`s` and nothing else. -/
theorem exh_Ici_univ (s : Set ι) : exh (alternatives univ) (Ici s) = {s} := by
  rw [exh_Ici, compl_univ, union_empty, Icc_self]

/-- Szabolcsi's coordination test, (12) against (13): the identificational *a hat* contradicts
the identificational *a hat and a coat*, while the information-focus *a hat* follows from the
information-focus *a hat and a coat*. -/
theorem szabolcsi_test (hb : b ∈ A) (hab : a ≠ b) :
    Disjoint (FocusType.identificational.interpret A (Ici {a, b}))
        (FocusType.identificational.interpret A (Ici {a})) ∧
      FocusType.information.interpret A (Ici {a, b}) ⊆
        FocusType.information.interpret A (Ici {a}) := by
  refine ⟨?_, Ici_subset_Ici.2 (singleton_subset_iff.2 (mem_insert a _))⟩
  rw [interpret_identificational, interpret_identificational, exh_Ici, exh_Ici, disjoint_left]
  rintro w ⟨hw, -⟩ ⟨-, hw'⟩
  rcases (mem_union _ _ _).1 (hw' (hw (mem_insert_of_mem a (mem_singleton b)))) with h | h
  · exact hab (mem_singleton_iff.1 h).symm
  · exact h hb

/-- Farkas's dialogue test, (15): where Mary picked a coat too, the identificational claim is
false, so *No, she picked a coat, too* denies its exhaustivity, while the information-focus
claim is true and the denial is out of place. -/
theorem farkas_test (hb : b ∈ A) (hab : a ≠ b) :
    {a, b} ∉ FocusType.identificational.interpret A (Ici {a}) ∧
      {a, b} ∈ FocusType.information.interpret A (Ici {a}) := by
  refine ⟨?_, singleton_subset_iff.2 (mem_insert a _)⟩
  rw [interpret_identificational, exh_Ici, mem_Icc, not_and]
  intro _ h
  rcases (mem_union _ _ _).1 (h (mem_insert_of_mem a (mem_singleton b))) with hba | hbA
  · exact hab (mem_singleton_iff.1 hba).symm
  · exact hbA hb

/-- Identificational focus fails the entailment that information focus passes: its
interpretation is not monotone in the prejacent. -/
theorem identificational_not_monotone (hb : b ∈ A) (hab : a ≠ b) :
    ¬ Monotone (FocusType.identificational.interpret A) := λ h =>
  (farkas_test hb hab).1 <| h (Ici_subset_Ici.2 (singleton_subset_iff.2 (mem_insert a _))) <| by
    rw [interpret_identificational, exh_Ici]
    exact left_mem_Icc.2 subset_union_left

theorem information_monotone (A : Set ι) :
    Monotone (FocusType.information.interpret A) := monotone_id

/-! ### Distributional restrictions (§3)

Exhaustive identification is exclusion by identification: an identificational focus names
the given elements the predicate holds of and excludes the rest. The constituents barred
from the identificational position, (17b–e), are those for which one half fails. -/

/-- A universal quantifier identifies without excluding (17b): over its restrictor, the
exhaustification of *every hat* is vacuous. -/
theorem exh_Ici_restrictor (A : Set ι) : exh (alternatives A) (Ici A) = Ici A := by
  rw [exh_Ici, union_compl_self, ← top_eq_univ, Icc_top]

/-- A *some*-phrase excludes without identifying (17e): the exhaustification of *something*
over a given set with two elements is contradictory. -/
theorem exh_nonempty_eq_empty (hA : A.Nontrivial) :
    exh (alternatives A) {w | (w ∩ A).Nonempty} = ∅ := by
  refine eq_empty_of_forall_notMem λ w hw => ?_
  obtain ⟨⟨i, hiw, hiA⟩, h⟩ := mem_exh.1 hw
  obtain ⟨j, hjA, hji⟩ := hA.exists_ne i
  exact hji (mem_singleton_iff.1 (singleton_subset_iff.1
    (h _ ⟨i, hiA, rfl⟩ (singleton_subset_iff.2 hiw) ⟨j, mem_singleton j, hjA⟩))).symm

/-- The additive presupposition of *also a* and *even a*: the predicate holds of some other
given element. -/
def additive (A : Set ι) (a : ι) : Set (Set ι) := {w | ∃ b ∈ w ∩ A, b ≠ a}

/-- An additive phrase identifies without excluding (17c, 17d): its presupposition
contradicts the exhaustification of its prejacent. -/
theorem disjoint_exh_additive (A : Set ι) (a : ι) :
    Disjoint (exh (alternatives A) (Ici {a})) (additive A a) := by
  rw [exh_Ici, disjoint_left]
  rintro w ⟨-, hw⟩ ⟨b, ⟨hbw, hbA⟩, hba⟩
  rcases hw hbw with h | h
  · exact hba h
  · exact h hbA

/-- The cleft *also*-phrase of (18): once a prior identification has removed `b` from the
given set, *it was also `a`* identifies `a` in addition, excluding everybody but `a` and `b`. -/
theorem additive_exh_of_notMem (hb : b ∉ A) (hab : b ≠ a) :
    {a, b} ∈ exh (alternatives A) (Ici {a}) ∩ additive (insert b A) a := by
  refine ⟨?_, b, ⟨mem_insert_of_mem a (mem_singleton b), mem_insert b A⟩, hab⟩
  rw [exh_Ici, mem_Icc, insert_subset_iff]
  exact ⟨singleton_subset_iff.2 (mem_insert a _), mem_union_left _ (mem_singleton a),
    singleton_subset_iff.2 (mem_union_right _ hb)⟩

end Kiss1998
