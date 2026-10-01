/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.SemigroupLangs`.
-/
module

public import Linglib.Core.Algebra.Semigroup.Pseudovariety
public import Linglib.Core.Computability.SyntacticSemigroup

/-!
# The languages of a semigroup pseudovariety

This file defines, for a pseudovariety `V` of finite semigroups, the languages whose syntactic
semigroup lies in `V`, and proves that over each alphabet they form a Boolean algebra closed under
quotients and inverse homomorphisms of free semigroups. These are Eilenberg's `+`-varieties, the
counterpart of `Monoid.Pseudovariety.langs` for languages of the free semigroup. The pseudovarieties
**D**, **K** and **LI** are varieties of semigroups and have no monoid counterpart.

## Main definitions

* `Semigroup.Pseudovariety.langs`: the languages whose syntactic semigroup lies in `V`.

## Main results

* `Semigroup.Pseudovariety.langs_of_recognizes`: a language recognized by a member of `V` lies in
  `V.langs`.
* `Semigroup.Pseudovariety.langs_leftQuotient`, `langs_rightQuotient`, `langs_comap`: closure under
  quotients and inverse homomorphisms of free semigroups.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

universe u

namespace Semigroup.Pseudovariety

open Language FreeSemigroup

variable (V : Pseudovariety.{u}) {α : Type u} {L M : Language α}

/-- The languages of a pseudovariety `V` are those whose syntactic semigroup lies in `V`. -/
def langs (L : Language α) : Prop := V.mem L.SyntacticSemigroup

theorem langs_isRegular (h : V.langs L) : L.IsRegular :=
  .of_finite_syntacticSemigroup (V.finite_of_mem h)

theorem langs_iff : V.langs L ↔ L.IsRegular ∧ V.mem L.SyntacticSemigroup :=
  ⟨fun h ↦ ⟨V.langs_isRegular h, h⟩, And.right⟩

variable {V} in
/-- The languages of `V` are upward closed in the order of syntactic congruences. -/
theorem langs_of_syntacticSemigroupCon_le (h : V.langs L)
    (hle : L.syntacticSemigroupCon ≤ M.syntacticSemigroupCon) : V.langs M :=
  V.mem_quotient_of_le hle h

/-- A language recognized by a member of `V` lies in `V.langs`. -/
theorem langs_of_recognizes {T : Type u} [Semigroup T] (hT : V.mem T)
    {η : FreeSemigroup α →ₙ* T} (h : L.RecognizesSemigroup η) : V.langs L :=
  V.mem_quotient_of_le (ker_le_syntacticSemigroupCon_of_recognizes h) (V.mem_quotient_ker η hT)

theorem langs_compl (h : V.langs L) : V.langs Lᶜ := by
  show V.mem (syntacticSemigroupCon Lᶜ).Quotient
  rw [syntacticSemigroupCon_compl]
  exact h

theorem langs_inf (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊓ M) :=
  V.mem_quotient_of_le inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf
    (V.mem_quotient_inf hL hM)

theorem langs_sup (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊔ M) := by
  rw [show L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ by rw [compl_inf, compl_compl, compl_compl]]
  exact V.langs_compl (V.langs_inf (V.langs_compl hL) (V.langs_compl hM))

theorem langs_univ : V.langs (⊤ : Language α) :=
  V.langs_of_recognizes V.memUnit (η := (1 : FreeSemigroup α →ₙ* PUnit.{u + 1}))
    (recognizesSemigroup_iff.mpr ⟨Set.univ, fun _ ↦ iff_of_true trivial (Set.mem_univ _)⟩)

theorem langs_bot : V.langs (⊥ : Language α) := by
  simpa using V.langs_compl V.langs_univ

/-- The languages of `V` are closed under inverse homomorphisms of free semigroups. A free
semigroup has no erasing homomorphisms, which is the difference from the monoid case. -/
theorem langs_comap {β : Type u} {Lb : Language β} (h : V.langs Lb)
    (φ : FreeSemigroup α →ₙ* FreeSemigroup β) :
    V.langs {w : List α | ∃ u : FreeSemigroup α,
      u.toFreeMonoid.toList = w ∧ (φ u).toFreeMonoid.toList ∈ Lb} := by
  refine V.langs_of_recognizes h (η := Lb.toSyntacticSemigroup.comp φ)
    (recognizesSemigroup_iff.mpr ⟨{m | ∃ u : FreeSemigroup β,
      Lb.toSyntacticSemigroup u = m ∧ u.toFreeMonoid.toList ∈ Lb}, fun w ↦ ⟨?_, ?_⟩⟩)
  · rintro ⟨u, hu, hmem⟩
    obtain rfl : u = w := toFreeMonoid_injective (FreeMonoid.toList.injective hu)
    exact ⟨φ u, rfl, hmem⟩
  · rintro ⟨v, hv, hmem⟩
    exact ⟨w, rfl, (SyntacticEquiv.mem_iff (toSyntacticSemigroup_eq_iff.mp hv)).mp hmem⟩

variable {V}

theorem langs_leftQuotient (h : V.langs L) (u : List α) : V.langs (L.leftQuotient u) :=
  langs_of_syntacticSemigroupCon_le h (L.syntacticSemigroupCon_le_leftQuotient u)

theorem langs_rightQuotient (h : V.langs L) (u : List α) : V.langs (L.rightQuotient u) :=
  langs_of_syntacticSemigroupCon_le h (L.syntacticSemigroupCon_le_rightQuotient u)

end Semigroup.Pseudovariety
