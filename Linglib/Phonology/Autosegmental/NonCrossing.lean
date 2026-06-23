/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Order.Monotone.Monovary

/-!
# Non-crossing constraint for two-layer association lines

A `Finset (ι × κ)` of links between two ordered tiers is **non-crossing**
when `k₁ < k₂ → i₁ ≤ i₂` for any two links `(k₁, i₁)`, `(k₂, i₂)` — i.e. the
index coordinates monovary, which in a two-layer drawing is exactly the
absence of crossing segments. This is the discrete-index
[goldsmith-1976] / [sagey-1986] No-Crossing Constraint and the canonical
filter on autosegmental GEN. It is built on mathlib's `MonovaryOn` rather
than graph planarity (which mathlib lacks and which would over-model it).

## Main declarations

* `IsNonCrossing links`: the link set monovaries (`[Preorder]`-general).
* `IndexCrosses links k i`: candidate `(k, i)` forms a crossing pair with
  some existing link — a 2-link set that fails `IsNonCrossing`. The
  decidable, `ℕ`-indexed GEN filter.

## Main results

* `monovaryOn_insert` / `monovaryOn_singleton`: the `Monovary` analogues of
  `Set.pairwise_insert` / `Set.pairwise_singleton`, absent from mathlib
  (`[UPSTREAM]` candidates). The structural keystones the rest derive from.
* `isNonCrossing_iff`: the elementary `∀∀→` form of `IsNonCrossing`.
* `IsNonCrossing.subset`: subset closure.
* `isNonCrossing_insert_iff'`: the insert-algebra — `insert p` stays
  non-crossing iff `p` is pairwise non-crossing with every existing link.
* `indexCrosses_iff`: the elementary index-ordering form of `IndexCrosses`.
* `isNonCrossing_insert_iff`: a candidate may be added iff it crosses
  nothing; `IsNonCrossing.insert_of_not_indexCrosses` is the GEN direction.
-/

namespace Autosegmental

/-! ### `MonovaryOn` on `insert` and singletons

`monovaryOn_insert` is the `Monovary` analogue of mathlib's
`Set.pairwise_insert` (which mathlib has, while the `MonovaryOn` version is
absent); both this and `monovaryOn_singleton` are `[UPSTREAM]` candidates for
`Mathlib/Order/Monotone/Monovary.lean`. -/

section Monovary
variable {ι α β : Type*} [Preorder α] [Preorder β] {f : ι → α} {g : ι → β}

/-- `MonovaryOn` holds vacuously on a singleton: there is only one index. -/
@[simp] theorem monovaryOn_singleton (a : ι) : MonovaryOn f g {a} := by
  rintro i rfl j rfl h
  exact absurd h (lt_irrefl _)

/-- `MonovaryOn` on `insert a s`: monovary on `s`, plus `a` does not invert the
    order against any element of `s`. The `Monovary` analogue of
    `Set.pairwise_insert` (the `a = b` diagonal is vacuous, so no `≠` guard). -/
theorem monovaryOn_insert {s : Set ι} {a : ι} :
    MonovaryOn f g (insert a s) ↔
      MonovaryOn f g s ∧ ∀ b ∈ s, (g a < g b → f a ≤ f b) ∧ (g b < g a → f b ≤ f a) := by
  refine ⟨fun h => ⟨h.subset (Set.subset_insert _ _),
      fun b hb => ⟨h (.inl rfl) (.inr hb), h (.inr hb) (.inl rfl)⟩⟩, ?_⟩
  rintro ⟨hs, hc⟩ i (rfl | hi) j (rfl | hj) hlt
  exacts [absurd hlt (lt_irrefl _), (hc j hj).1 hlt, (hc i hi).2 hlt, hs hi hj hlt]

end Monovary

/-! ### Set-level non-crossing property (via mathlib `MonovaryOn`) -/

section
variable {ι κ : Type*} [Preorder ι] [Preorder κ] (links : Finset (ι × κ))

/-- The link set has no crossings: its two index coordinates monovary. -/
def IsNonCrossing : Prop :=
  MonovaryOn Prod.snd Prod.fst (↑links : Set (ι × κ))

/-- `IsNonCrossing` in elementary form. -/
theorem isNonCrossing_iff : IsNonCrossing links ↔
    ∀ l₁ ∈ links, ∀ l₂ ∈ links, l₁.fst < l₂.fst → l₁.snd ≤ l₂.snd := Iff.rfl

@[simp] theorem isNonCrossing_empty : IsNonCrossing (∅ : Finset (ι × κ)) := by
  simp [IsNonCrossing]

@[simp] theorem isNonCrossing_singleton (p : ι × κ) : IsNonCrossing {p} := by
  simp [IsNonCrossing]

/-- A pair is non-crossing iff its two links agree in tier- and backbone-order. -/
theorem isNonCrossing_pair [DecidableEq ι] [DecidableEq κ] (a b : ι × κ) :
    IsNonCrossing {a, b} ↔ (a.1 < b.1 → a.2 ≤ b.2) ∧ (b.1 < a.1 → b.2 ≤ a.2) := by
  simp [IsNonCrossing, monovaryOn_insert]

/-- A subset of a non-crossing link set is non-crossing. -/
theorem IsNonCrossing.subset {s t : Finset (ι × κ)} (hst : s ⊆ t)
    (h : IsNonCrossing t) : IsNonCrossing s :=
  MonovaryOn.subset (Finset.coe_subset.mpr hst) h

/-- Inserting `p` keeps non-crossing iff `p` crosses no existing link: the
    insert-algebra form, `Set.pairwise_insert` specialised to `IsNonCrossing`
    via `monovaryOn_insert`. -/
theorem isNonCrossing_insert_iff' [DecidableEq ι] [DecidableEq κ] (p : ι × κ) :
    IsNonCrossing (insert p links) ↔
      IsNonCrossing links ∧ ∀ q ∈ links, IsNonCrossing {p, q} := by
  simp only [IsNonCrossing, Finset.coe_insert, Finset.coe_singleton, monovaryOn_insert,
    monovaryOn_singleton, Finset.mem_coe, Set.mem_singleton_iff, forall_eq, true_and]

instance [DecidableLT ι] [DecidableLE κ] :
    Decidable (IsNonCrossing links) :=
  decidable_of_iff _ (isNonCrossing_iff links).symm

end

/-! ### Candidate-level crossing predicate (`ℕ`-indexed GEN filter) -/

section
variable (links : Finset (ℕ × ℕ)) (k i : ℕ)

/-- `(k, i)` crosses some link in `links` — the decidable GEN filter. -/
def IndexCrosses : Prop :=
  ∃ l ∈ links, ¬ IsNonCrossing {(k, i), l}

instance : Decidable (IndexCrosses links k i) := by unfold IndexCrosses; infer_instance

/-- `IndexCrosses` in elementary index-ordering form. -/
theorem indexCrosses_iff :
    IndexCrosses links k i ↔
      ∃ l ∈ links, (k < l.fst ∧ l.snd < i) ∨ (l.fst < k ∧ i < l.snd) := by
  simp only [IndexCrosses, isNonCrossing_pair]
  exact exists_congr fun _ => and_congr_right fun _ => by omega

end

section
variable {links : Finset (ℕ × ℕ)} {k i : ℕ}

/-- `(k, i)` crosses nothing iff it is pairwise non-crossing with every link. -/
theorem not_indexCrosses_iff :
    ¬ IndexCrosses links k i ↔ ∀ l ∈ links, IsNonCrossing {(k, i), l} := by
  simp only [IndexCrosses, not_exists, not_and, not_not]

/-- Adding `(k, i)` keeps non-crossing iff it crosses no existing link. The two
    structural facts: `isNonCrossing_insert_iff'` (the insert-algebra) and
    `not_indexCrosses_iff` (the De Morgan dual of the GEN filter). -/
theorem isNonCrossing_insert_iff :
    IsNonCrossing (insert (k, i) links) ↔
      IsNonCrossing links ∧ ¬ IndexCrosses links k i := by
  rw [isNonCrossing_insert_iff', not_indexCrosses_iff]

/-- GEN direction of `isNonCrossing_insert_iff`. -/
theorem IsNonCrossing.insert_of_not_indexCrosses
    (hNC : IsNonCrossing links) (hNX : ¬ IndexCrosses links k i) :
    IsNonCrossing (insert (k, i) links) :=
  isNonCrossing_insert_iff.mpr ⟨hNC, hNX⟩

end

end Autosegmental
