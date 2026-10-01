/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.Langs`, a new topic directory over
`Mathlib.Algebra.Group.Pseudovariety`.
-/
module

public import Linglib.Core.Computability.SyntacticMonoid
public import Linglib.Core.Algebra.Group.Pseudovariety
public import Mathlib.Order.BooleanSubalgebra

/-!
# The languages of a pseudovariety

This file defines, for a pseudovariety `V` of finite monoids, the languages whose syntactic monoid
lies in `V`, and proves that over each alphabet they form a Boolean algebra closed under quotients
and inverse homomorphisms. These closure properties make `V.langs` a variety of languages, the
language side of Eilenberg's variety theorem.

## Main definitions

* `Monoid.Pseudovariety.langs`: the languages whose syntactic monoid lies in `V`.
* `Monoid.Pseudovariety.toBooleanSubalgebra`: the languages of `V` over an alphabet, as a Boolean
  subalgebra.

## Main results

* `Monoid.Pseudovariety.langs_of_recognizes`: a language recognized by a member of `V` lies in
  `V.langs`.
* `Monoid.Pseudovariety.langs_leftQuotient`, `langs_rightQuotient`, `langs_comap`: closure under
  quotients and inverse homomorphisms.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

universe u

namespace Monoid.Pseudovariety

open Language

variable (V : Pseudovariety.{u}) {α : Type u} {L M : Language α}

/-- The languages of a pseudovariety `V` are those whose syntactic monoid lies in `V`. -/
def langs (L : Language α) : Prop := V.mem L.SyntacticMonoid

theorem langs_isRegular (h : V.langs L) : L.IsRegular :=
  .of_finite_syntacticMonoid (V.finite_of_mem h)

theorem langs_iff : V.langs L ↔ L.IsRegular ∧ V.mem L.SyntacticMonoid :=
  ⟨fun h ↦ ⟨V.langs_isRegular h, h⟩, And.right⟩

variable {V} in
/-- The languages of `V` are upward closed in the order of syntactic congruences. -/
theorem langs_of_syntacticCon_le (h : V.langs L) (hle : L.syntacticCon ≤ M.syntacticCon) :
    V.langs M :=
  V.mem_quotient_of_le hle h

/-- A language recognized by a member of `V` lies in `V.langs`. -/
theorem langs_of_recognizes {N : Type u} [Monoid N] (hN : V.mem N) {η : FreeMonoid α →* N}
    (h : Recognizes η L) : V.langs L :=
  V.mem_quotient_of_le (ker_le_syntacticCon_of_recognizes h) (V.mem_quotient_ker η hN)

theorem langs_compl (h : V.langs L) : V.langs Lᶜ := by
  show V.mem (syntacticCon Lᶜ).Quotient
  rw [syntacticCon_compl]
  exact h

theorem langs_inf (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊓ M) :=
  V.mem_quotient_of_le inf_syntacticCon_le_syntacticCon_inf (V.mem_quotient_inf hL hM)

theorem langs_sup (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊔ M) := by
  rw [show L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ by rw [compl_inf, compl_compl, compl_compl]]
  exact V.langs_compl (V.langs_inf (V.langs_compl hL) (V.langs_compl hM))

theorem langs_univ : V.langs (⊤ : Language α) :=
  V.langs_of_recognizes V.memUnit (η := (1 : FreeMonoid α →* PUnit.{u + 1})) ⟨Set.univ, rfl⟩

theorem langs_bot : V.langs (⊥ : Language α) := by
  simpa using V.langs_compl V.langs_univ

/-- The languages of `V` are closed under inverse homomorphisms of free monoids. -/
theorem langs_comap {β : Type u} {Lb : Language β} (h : V.langs Lb)
    (φ : FreeMonoid α →* FreeMonoid β) :
    V.langs {w : List α | φ (FreeMonoid.ofList w) ∈ Lb} := by
  obtain ⟨S, hS⟩ := Lb.recognizes_toSyntacticMonoid
  exact V.langs_of_recognizes h (η := Lb.toSyntacticMonoid.comp φ)
    ⟨S, Set.ext fun w ↦ Set.ext_iff.mp hS (φ (FreeMonoid.ofList w))⟩

variable {V}

theorem langs_leftQuotient (h : V.langs L) (u : List α) : V.langs (L.leftQuotient u) :=
  langs_of_syntacticCon_le h (L.syntacticCon_le_leftQuotient u)

theorem langs_rightQuotient (h : V.langs L) (u : List α) : V.langs (L.rightQuotient u) :=
  langs_of_syntacticCon_le h (L.syntacticCon_le_rightQuotient u)

variable (V) in
/-- The languages of `V` over `α`, as a Boolean subalgebra of `Language α`. -/
def toBooleanSubalgebra (α : Type u) : BooleanSubalgebra (Language α) where
  carrier := {L | V.langs L}
  supClosed' _ hL _ hM := V.langs_sup hL hM
  infClosed' _ hL _ hM := V.langs_inf hL hM
  compl_mem' h := V.langs_compl h
  bot_mem' := V.langs_bot

@[simp] theorem mem_toBooleanSubalgebra : L ∈ V.toBooleanSubalgebra α ↔ V.langs L := Iff.rfl

end Monoid.Pseudovariety
