/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Logic.Function.Basic` for the idempotent form,
`Mathlib.Data.Set.Finite.Range` and `Mathlib.SetTheory.Cardinal.Finite` for the range lemmas.
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Functions that factor through another

Lemmas on mathlib's `Function.FactorsThrough`. A function that factors through `f` takes no more
values than `f`, and factoring through an idempotent function is invariance under it.

Factoring through on a subset `s` needs no predicate of its own. It is
`(s.domRestrict g).FactorsThrough (s.domRestrict f)`, and `Function.factorsThrough_iff` then says
that `g` agrees on `s` with a function of `f`.

## Main results

* `Function.FactorsThrough.finite_range`, `Function.FactorsThrough.card_range_le`: a function that
  factors through another takes no more values, so its range is finite when the other's is.
* `Function.factorsThrough_iff_of_idempotent`: a function factors through an idempotent `f`
  exactly when it is invariant under `f`.
-/

@[expose] public section

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*} {g : α → γ} {f : α → β}

/-- A function factors through an idempotent `f` exactly when it is invariant under `f`. -/
theorem factorsThrough_iff_of_idempotent {f : α → α} (hf : ∀ a, f (f a) = f a) :
    FactorsThrough g f ↔ ∀ a, g a = g (f a) :=
  ⟨fun h a ↦ h (hf a).symm, fun h a b hab ↦ (h a).trans ((congrArg g hab).trans (h b).symm)⟩

instance [Fintype α] [DecidableEq β] [DecidableEq γ] : Decidable (FactorsThrough g f) := by
  unfold FactorsThrough; infer_instance

/-- A function that factors through another takes no more values. -/
theorem FactorsThrough.card_range_le [Finite α] (h : FactorsThrough g f) :
    Nat.card (Set.range g) ≤ Nat.card (Set.range f) := by
  refine Nat.card_le_card_of_surjective (fun b ↦ ⟨g b.2.choose, b.2.choose, rfl⟩) ?_
  rintro ⟨_, a, rfl⟩
  exact ⟨⟨f a, a, rfl⟩, Subtype.ext (h (⟨a, rfl⟩ : ∃ a', f a' = f a).choose_spec)⟩

/-- A function that factors through a function with finite range has finite range. -/
theorem FactorsThrough.finite_range (h : FactorsThrough g f) (hf : (Set.range f).Finite) :
    (Set.range g).Finite := by
  have := hf.to_subtype
  refine (Set.finite_range fun b : Set.range f ↦ g b.2.choose).subset ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨f a, a, rfl⟩, h (⟨a, rfl⟩ : ∃ a', f a' = f a).choose_spec⟩

end Function
