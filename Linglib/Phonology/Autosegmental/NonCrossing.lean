/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Linglib.Core.Order.Monotone.Monovary

/-!
# Non-crossing constraint for two-layer association lines

A `Finset (ι × κ)` of links between two ordered tiers is **non-crossing**
when `k₁ < k₂ → i₁ ≤ i₂` for any two links `(k₁, i₁)`, `(k₂, i₂)` — i.e. the
index coordinates monovary, which in a two-layer drawing is exactly the
absence of crossing segments. This is the discrete-index
[goldsmith-1976] / [sagey-1986] No-Crossing Constraint and the canonical
filter on autosegmental GEN.

## Main declarations

* `IsNonCrossing links`: the link set monovaries (`[Preorder]`-general).
* `IndexCrosses links k i`: `(k, i)` crosses an existing link — decidable, `ℕ`-indexed GEN filter.

## Main results

* `isNonCrossing_iff`: the elementary `∀∀→` form of `IsNonCrossing`.
* `IsNonCrossing.subset`: subset closure.
* `isNonCrossing_insert_iff'`: the insert-algebra — `insert p` stays
  non-crossing iff `p` is pairwise non-crossing with every existing link.
* `indexCrosses_iff`: the elementary index-ordering form of `IndexCrosses`.
* `isNonCrossing_insert_iff`: a candidate may be added iff it crosses
  nothing; `IsNonCrossing.insert_of_not_indexCrosses` is the GEN direction.
-/

namespace Autosegmental

/-! ### Set-level non-crossing property (via mathlib `MonovaryOn`) -/

section
variable {ι κ : Type*} [Preorder ι] [Preorder κ] (links : Finset (ι × κ))

/-- The link set has no crossings: its two index coordinates monovary. -/
def IsNonCrossing : Prop := MonovaryOn Prod.snd Prod.fst (↑links : Set (ι × κ))

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

/-- Pushing a non-crossing link set forward along a **monotone** map on the upper
    (first) coordinate keeps it non-crossing: the autosegmental analogue of
    `SimpleGraph.map` along a monotone vertex map. The upper index needs a
    `LinearOrder` (the run-collapse domain is `ℕ`) so that `ρ` reflects `<`. Used to
    lift planarity through the OCP run-collapse `ρ` (`Autosegmental/Collapse.lean`). -/
theorem IsNonCrossing.image_monotone {ι ι' κ : Type*} [LinearOrder ι] [Preorder ι']
    [Preorder κ] [DecidableEq ι'] [DecidableEq κ] {links : Finset (ι × κ)}
    {ρ : ι → ι'} (hρ : Monotone ρ) (h : IsNonCrossing links) :
    IsNonCrossing (links.image (Prod.map ρ id)) := by
  rw [isNonCrossing_iff] at h ⊢
  rintro _ hl₁ _ hl₂ hlt
  simp only [Finset.mem_image, Prod.exists, Prod.map_apply, id_eq] at hl₁ hl₂
  obtain ⟨k₁, i₁, hp₁, rfl⟩ := hl₁
  obtain ⟨k₂, i₂, hp₂, rfl⟩ := hl₂
  have hlt' : ρ k₁ < ρ k₂ := hlt
  exact h _ hp₁ _ hp₂ (hρ.reflect_lt hlt')

/-- Inserting `p` keeps non-crossing iff `p` crosses no existing link: the
    insert-algebra form, `Set.pairwise_insert` specialised to `IsNonCrossing`
    via `monovaryOn_insert`. -/
theorem isNonCrossing_insert_iff' [DecidableEq ι] [DecidableEq κ] (p : ι × κ) :
    IsNonCrossing (insert p links) ↔
      IsNonCrossing links ∧ ∀ q ∈ links, IsNonCrossing {p, q} := by
  simp [IsNonCrossing, monovaryOn_insert]

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
