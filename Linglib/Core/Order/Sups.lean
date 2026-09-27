module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.SupClosed
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Hom.Basic

/-!
# Closure properties of pointwise sups of sets

For sets `s t` in a semilattice, `s ⊻ t` is the set of sups `a ⊔ b` with `a ∈ s` and
`b ∈ t` (`Set.sups`). This file records which closure properties `⊻` preserves: sup-closure
and the bottom element in any semilattice, downward closure and order-convexity (the latter
given sup-closure) in a distributive lattice, where `c ≤ a ⊔ b` splits as
`c = (c ⊓ a) ⊔ (c ⊓ b)`. It also records that the preimage of a set containing `⊥` under a
bottom-preserving map contains `⊥`, the companion of `SupClosed.preimage` and
`IsLowerSet.preimage`.

## Main results

* `SupClosed.sups`, `Set.bot_mem_sups` — in a semilattice.
* `IsLowerSet.sups`, `Set.OrdConnected.sups` — in a distributive lattice.
* `bot_mem_preimage` — for a `BotHomClass` map.
-/

@[expose] public section

open scoped SetFamily

variable {α : Type*}

section SemilatticeSup

variable [SemilatticeSup α] {s t : Set α}

theorem SupClosed.sups (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ⊻ t) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_sups.mp hy
  exact Set.mem_sups.mpr ⟨a ⊔ c, hs ha hc, b ⊔ d, ht hb hd, (sup_sup_sup_comm a b c d).symm⟩

theorem Set.bot_mem_sups [OrderBot α] (hs : ⊥ ∈ s) (ht : ⊥ ∈ t) : ⊥ ∈ s ⊻ t :=
  Set.mem_sups.mpr ⟨⊥, hs, ⊥, ht, bot_sup_eq ⊥⟩

end SemilatticeSup

section DistribLattice

variable [DistribLattice α] {s t : Set α}

theorem IsLowerSet.sups (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ⊻ t) := by
  intro x c hc hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hx
  exact Set.mem_sups.mpr ⟨c ⊓ a, hs inf_le_right ha, c ⊓ b, ht inf_le_right hb,
    by rw [← inf_sup_left, inf_eq_left.mpr hc]⟩

/-- Pointwise sups of convex sets are convex when both sets are sup-closed: an element
    `x` between `a ⊔ b` and `c ⊔ d` splits as `(a ⊔ c) ⊓ x ⊔ (b ⊔ d) ⊓ x`, each part lying
    between `a` and `a ⊔ c`, respectively `b` and `b ⊔ d`. -/
theorem Set.OrdConnected.sups (hs : s.OrdConnected) (ht : t.OrdConnected) (hs' : SupClosed s)
    (ht' : SupClosed t) : (s ⊻ t).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro y hy z hz hle x ⟨hx₁, hx₂⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hy
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_sups.mp hz
  refine Set.mem_sups.mpr ⟨(a ⊔ c) ⊓ x, hs.out ha (hs' ha hc)
      ⟨le_inf le_sup_left (le_sup_left.trans hx₁), inf_le_left⟩, (b ⊔ d) ⊓ x,
      ht.out hb (ht' hb hd) ⟨le_inf le_sup_left (le_sup_right.trans hx₁), inf_le_left⟩, ?_⟩
  rw [← inf_sup_right, sup_sup_sup_comm, sup_eq_right.mpr hle, inf_eq_right.mpr hx₂]

end DistribLattice

theorem bot_mem_preimage {β F : Type*} [Bot α] [Bot β] [FunLike F α β] [BotHomClass F α β]
    (f : F) {P : Set β} (hP : ⊥ ∈ P) : ⊥ ∈ f ⁻¹' P := by
  simpa [Set.mem_preimage, map_bot] using hP
