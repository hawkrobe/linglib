/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Order.Disjoint
import Mathlib.Order.ModularLattice
import Mathlib.Order.Monotone.Defs

/-!
# Valuations on lattices

A *valuation* on a lattice is a function `v` into an additive commutative
monoid satisfying the modular law `v (a ⊔ b) + v (a ⊓ b) = v a + v b`; it is
*positive* when it is strictly monotone. Cardinality of finite sets is the
model example (`Finset.card`), and finitely additive set functions —
`MeasureTheory.AddContent` on a ring of sets, a measure on the measurable
sets — are the set-lattice instances. Mathlib states the modular law per
instance (`Finset.card_union_add_card_inter`, `Set.ncard_union_add_ncard_inter`,
`MeasureTheory.measure_union_add_inter`) with no common structure; this file
supplies it, together with Birkhoff's theorem that a lattice carrying a
positive valuation is modular. `[UPSTREAM]` candidate.

## Main declarations

* `IsLatticeValuation v` — the modular law; additive on disjoint pairs once
  `v ⊥ = 0` (`IsLatticeValuation.map_sup_of_disjoint`).
* `IsPositiveValuation v` — a strictly monotone valuation.
* `IsPositiveValuation.isModularLattice` — a lattice with a positive
  valuation into a cancellative monoid is modular.
* `Finset.card` is a positive valuation.

## References

* [birkhoff-1967], Chapter X
-/

variable {α M : Type*}

/-- A lattice valuation: `v (a ⊔ b) + v (a ⊓ b) = v a + v b`. -/
class IsLatticeValuation [Lattice α] [AddCommMonoid M] (v : α → M) : Prop where
  map_sup_add_map_inf (a b : α) : v (a ⊔ b) + v (a ⊓ b) = v a + v b

export IsLatticeValuation (map_sup_add_map_inf)

/-- A positive valuation: a strictly monotone lattice valuation. -/
class IsPositiveValuation [Lattice α] [AddCommMonoid M] [Preorder M] (v : α → M) : Prop
    extends IsLatticeValuation v where
  strictMono : StrictMono v

namespace IsLatticeValuation

variable [Lattice α] [OrderBot α] [AddCommMonoid M] (v : α → M) [IsLatticeValuation v]
  {a b : α}

/-- A valuation vanishing at `⊥` is additive on disjoint pairs. -/
theorem map_sup_of_disjoint (h0 : v ⊥ = 0) (h : Disjoint a b) : v (a ⊔ b) = v a + v b := by
  simpa [h.eq_bot, h0] using map_sup_add_map_inf (v := v) a b

end IsLatticeValuation

namespace IsPositiveValuation

variable [Lattice α] [AddCommMonoid M] [Preorder M]

/-- A lattice carrying a positive valuation into a cancellative monoid is
modular: for `x ≤ z`, the elements `x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z` have the same join
and meet with `y`, hence the same valuation, hence coincide. -/
theorem isModularLattice [IsRightCancelAdd M] (v : α → M) [IsPositiveValuation v] :
    IsModularLattice α where
  sup_inf_le_assoc_of_le {x} y {z} hxz := by
    have hab : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
      sup_le (le_inf le_sup_left hxz) (inf_le_inf_right z le_sup_right)
    have h₁ : (x ⊔ y ⊓ z) ⊔ y = ((x ⊔ y) ⊓ z) ⊔ y :=
      le_antisymm (sup_le_sup_right hab y)
        (sup_le (inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
          le_sup_right)
    have h₂ : (x ⊔ y ⊓ z) ⊓ y = ((x ⊔ y) ⊓ z) ⊓ y :=
      le_antisymm (inf_le_inf_right y hab)
        (le_inf ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans le_sup_right)
          inf_le_right)
    have h := map_sup_add_map_inf (v := v) (x ⊔ y ⊓ z) y
    rw [h₁, h₂] at h
    have hv : v (x ⊔ y ⊓ z) = v ((x ⊔ y) ⊓ z) :=
      add_right_cancel (h.symm.trans (map_sup_add_map_inf (v := v) ((x ⊔ y) ⊓ z) y))
    exact hab.lt_or_eq.elim (fun hlt => absurd hv (strictMono (v := v) hlt).ne) fun heq => heq.ge

end IsPositiveValuation

instance [DecidableEq α] : IsPositiveValuation (Finset.card : Finset α → ℕ) where
  map_sup_add_map_inf := Finset.card_union_add_card_inter
  strictMono := Finset.card_strictMono

example [DecidableEq α] {s t : Finset α} (h : Disjoint s t) : (s ∪ t).card = s.card + t.card :=
  IsLatticeValuation.map_sup_of_disjoint Finset.card Finset.card_empty h
