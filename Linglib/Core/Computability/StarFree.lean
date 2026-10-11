/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.StarFree`, after the
syntactic-monoid and variety substrate.
-/
module

public import Mathlib.Order.CompleteLattice.Finset
public import Linglib.Core.Computability.Variety.Langs

/-!
# Star-free languages

This file defines the star-free languages as the regular languages with an aperiodic syntactic
monoid. By Schützenberger's theorem these are the languages of the star-free regular expressions,
built from finite sets by union, concatenation and complement without Kleene star; McNaughton and
Papert show that they are also the counter-free and the first-order definable languages. Star-free
is the instance `Monoid.aperiodicVariety` of the languages of a pseudovariety, so its closure
properties are corollaries of `Monoid.Pseudovariety.langs`.

## Main definitions

* `Language.IsStarFree`: the languages of `Monoid.aperiodicVariety`.

## Main results

* `Language.isStarFree_iff`: a language is star-free exactly when it is regular with an aperiodic
  syntactic monoid.
* `Language.IsStarFree.compl`, `Language.IsStarFree.inter`, `Language.IsStarFree.union`: Boolean
  closure.
* `Language.IsStarFree.of_recognizes`: a language recognized by a finite aperiodic monoid is
  star-free.
* `Language.IsStarFree.comap`: closure under inverse homomorphisms, with the erasing instance
  `Language.IsStarFree.preimage_filter`.

## References

* [schutzenberger-1965]
* [mcnaughton-papert-1971]
-/

@[expose] public section

namespace Language

variable {α : Type*} {L : Language α}

/-- A language is *star-free* when its syntactic monoid is finite and aperiodic, that is, when it
is a language of the pseudovariety of aperiodic monoids. -/
def IsStarFree (L : Language α) : Prop := Monoid.aperiodicVariety.langs L

/-- A language is star-free exactly when it is regular with an aperiodic syntactic monoid. -/
theorem isStarFree_iff : L.IsStarFree ↔ L.IsRegular ∧ Monoid.IsAperiodic L.SyntacticMonoid :=
  ⟨fun h ↦ ⟨.of_finite_syntacticMonoid h.1, h.2⟩, fun h ↦ ⟨h.1.finite_syntacticMonoid, h.2⟩⟩

theorem IsStarFree.isRegular (h : L.IsStarFree) : L.IsRegular := .of_finite_syntacticMonoid h.1

theorem IsStarFree.isAperiodic (h : L.IsStarFree) :
    Monoid.IsAperiodic L.SyntacticMonoid := h.2

/-- Star-free languages are closed under complement. -/
theorem IsStarFree.compl (h : L.IsStarFree) : Lᶜ.IsStarFree :=
  Monoid.aperiodicVariety.langs_compl h

/-- Star-free languages are closed under intersection. -/
theorem IsStarFree.inter {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊓ M).IsStarFree :=
  Monoid.aperiodicVariety.langs_inf hL hM

/-- Star-free languages are closed under union. -/
theorem IsStarFree.union {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊔ M).IsStarFree :=
  Monoid.aperiodicVariety.langs_sup hL hM

/-- A language recognized by a finite aperiodic monoid is star-free. Unlike
`Monoid.Pseudovariety.langs_of_recognizes`, the recognizer may live in any universe. -/
theorem IsStarFree.of_recognizes {M : Type*} [Monoid M] [Finite M]
    (hM : Monoid.IsAperiodic M) (η : FreeMonoid α →* M) (P : Set M)
    (hL : ∀ w : List α, w ∈ L ↔ η (FreeMonoid.ofList w) ∈ P) : L.IsStarFree := by
  obtain ⟨N, f, hf⟩ := Recognizes.syntacticMonoid_isSubquotient (φ := η) ⟨P, Set.ext hL⟩
  exact ⟨.of_surjective f hf, (hM.of_injective N.subtype_injective).of_surjective hf⟩

/-- Star-free languages are closed under inverse homomorphisms of free monoids. -/
theorem IsStarFree.comap {α β : Type*} {L : Language β} (h : L.IsStarFree)
    (φ : FreeMonoid α →* FreeMonoid β) :
    Language.IsStarFree {w : List α | φ (FreeMonoid.ofList w) ∈ L} := by
  have := h.1
  obtain ⟨S, hS⟩ := L.recognizes_toSyntacticMonoid.comap φ
  exact .of_recognizes h.2 _ S (Set.ext_iff.mp hS)

/-- Star-free languages are closed under preimage by erasure, the instance of `IsStarFree.comap`
for the homomorphism `List.filter p` that erases the letters failing `p`. -/
theorem IsStarFree.preimage_filter (h : L.IsStarFree) (p : α → Bool) :
    IsStarFree {w | w.filter p ∈ L} := by
  have e (w : List α) : (FreeMonoid.lift fun a ↦ if p a then FreeMonoid.of a else 1)
      (FreeMonoid.ofList w) = FreeMonoid.ofList (w.filter p) := by
    induction w with
    | nil => rfl
    | cons a w ih =>
      rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of, ih, List.filter_cons]
      split <;> rfl
  have := h.comap (FreeMonoid.lift fun a ↦ if p a then FreeMonoid.of a else 1)
  simp only [e] at this
  exact this

/-- The full language is star-free. -/
theorem isStarFree_univ : IsStarFree (Set.univ : Language α) :=
  Monoid.aperiodicVariety.langs_univ

/-- Star-free languages are closed under finitely-indexed intersections. -/
theorem IsStarFree.iInter {ι : Type*} [Finite ι] {f : ι → Set (List α)}
    (h : ∀ i, IsStarFree (f i)) : IsStarFree (⋂ i, f i) := by
  have := Fintype.ofFinite ι
  classical
  rw [show (⋂ i, f i) = ⋂ i ∈ (Finset.univ : Finset ι), f i by simp]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using isStarFree_univ
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a).inter ih

end Language
