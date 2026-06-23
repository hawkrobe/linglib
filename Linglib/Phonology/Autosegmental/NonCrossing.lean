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

* `isNonCrossing_iff`: the elementary `∀∀→` form of `IsNonCrossing`.
* `IsNonCrossing.subset`: subset closure.
* `indexCrosses_iff`: the elementary index-ordering form of `IndexCrosses`.
* `isNonCrossing_insert_iff`: a candidate may be added iff it crosses
  nothing; `IsNonCrossing.insert_of_not_indexCrosses` is the GEN direction.
-/

namespace Autosegmental

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
  simp [isNonCrossing_iff]

/-- A pair is non-crossing iff its two links agree in tier- and backbone-order. -/
theorem isNonCrossing_pair [DecidableEq ι] [DecidableEq κ] (a b : ι × κ) :
    IsNonCrossing {a, b} ↔ (a.1 < b.1 → a.2 ≤ b.2) ∧ (b.1 < a.1 → b.2 ≤ a.2) := by
  simp [isNonCrossing_iff]

/-- A subset of a non-crossing link set is non-crossing. -/
theorem IsNonCrossing.subset {s t : Finset (ι × κ)} (hst : s ⊆ t)
    (h : IsNonCrossing t) : IsNonCrossing s :=
  MonovaryOn.subset (Finset.coe_subset.mpr hst) h

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

/-- Adding `(k, i)` keeps non-crossing iff it crosses no existing link. -/
theorem isNonCrossing_insert_iff :
    IsNonCrossing (insert (k, i) links) ↔
      IsNonCrossing links ∧ ¬ IndexCrosses links k i := by
  simp only [isNonCrossing_iff, indexCrosses_iff, Finset.mem_insert,
    not_exists, not_or, not_and, not_lt]
  constructor
  · intro h
    exact ⟨fun l₁ hl₁ l₂ hl₂ => h l₁ (.inr hl₁) l₂ (.inr hl₂),
      fun l hl => ⟨h (k, i) (.inl rfl) l (.inr hl), h l (.inr hl) (k, i) (.inl rfl)⟩⟩
  · rintro ⟨hNC, hX⟩ l₁ (rfl | hl₁) l₂ (rfl | hl₂) hlt
    · omega
    · exact (hX l₂ hl₂).1 hlt
    · exact (hX l₁ hl₁).2 hlt
    · exact hNC l₁ hl₁ l₂ hl₂ hlt

/-- GEN direction of `isNonCrossing_insert_iff`. -/
theorem IsNonCrossing.insert_of_not_indexCrosses
    (hNC : IsNonCrossing links) (hNX : ¬ IndexCrosses links k i) :
    IsNonCrossing (insert (k, i) links) :=
  isNonCrossing_insert_iff.mpr ⟨hNC, hNX⟩

end

end Autosegmental
