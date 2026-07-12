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
absence of crossing segments; equivalently (over linear tiers), the
componentwise order is total on the link set, [yli-jyra-2015]'s edge-order
axiom. This is the discrete-index
[goldsmith-1976] / [sagey-1986] No-Crossing Constraint and the canonical
filter on autosegmental GEN.

## Main definitions

* `IsNonCrossing links`: the link set monovaries (`[Preorder]`-general).
* `Crosses a b` / `IndexCrosses links p`: two links cross; `p` crosses some link
  already in `links` — the decidable GEN filter.

## Main results

* `isNonCrossing_insert_iff_not_indexCrosses`: a candidate may be added iff it
  crosses nothing (`IsNonCrossing.insert_of_not_indexCrosses` is the GEN direction).
* `isNonCrossing_image` / `IsNonCrossing.image_monotone`: `IsNonCrossing` commutes
  with `Finset.image`, and survives monotone reindexing of the upper coordinate.
-/

namespace Autosegmental

variable {ι ι' κ κ' : Type*}

/-! ### Set-level non-crossing property (via mathlib `MonovaryOn`) -/

section Preorder
variable [Preorder ι] [Preorder κ] {links : Finset (ι × κ)}

/-- The link set has no crossings: its two index coordinates monovary. -/
def IsNonCrossing (links : Finset (ι × κ)) : Prop :=
  MonovaryOn Prod.snd Prod.fst (↑links : Set (ι × κ))

/-- `IsNonCrossing` in elementary form. -/
theorem isNonCrossing_iff : IsNonCrossing links ↔
    ∀ l₁ ∈ links, ∀ l₂ ∈ links, l₁.1 < l₂.1 → l₁.2 ≤ l₂.2 := Iff.rfl

@[simp] theorem isNonCrossing_empty : IsNonCrossing (∅ : Finset (ι × κ)) := by simp [IsNonCrossing]

@[simp] theorem isNonCrossing_singleton (p : ι × κ) : IsNonCrossing {p} := by simp [IsNonCrossing]

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
theorem isNonCrossing_insert_iff [DecidableEq ι] [DecidableEq κ] (p : ι × κ) :
    IsNonCrossing (insert p links) ↔
      IsNonCrossing links ∧ ∀ q ∈ links, IsNonCrossing {p, q} := by
  simp [IsNonCrossing, monovaryOn_insert]

instance [DecidableLT ι] [DecidableLE κ] : Decidable (IsNonCrossing links) :=
  decidable_of_iff _ isNonCrossing_iff.symm

end Preorder

/-! ### Reindexing along `Finset.image` -/

section Image
variable [Preorder ι'] [Preorder κ'] [DecidableEq ι'] [DecidableEq κ'] {links : Finset (ι × κ)}

/-- `IsNonCrossing` transports across a `Finset.image`: the image link set is
    non-crossing iff the index coordinates monovary after reindexing by `f`. The
    `Finset` companion of `monovaryOn_image`, and the single place the definition
    is unfolded against an image. -/
theorem isNonCrossing_image (f : ι × κ → ι' × κ') :
    IsNonCrossing (links.image f) ↔
      MonovaryOn (Prod.snd ∘ f) (Prod.fst ∘ f) (↑links : Set (ι × κ)) := by
  simp only [IsNonCrossing, Finset.coe_image, monovaryOn_image]

end Image

section ImageMonotone
variable [LinearOrder ι] [Preorder ι'] [Preorder κ] [DecidableEq ι'] [DecidableEq κ]
  {links : Finset (ι × κ)} {ρ : ι → ι'}

/-- Pushing a non-crossing link set forward along a **monotone** map on the upper
    (first) coordinate keeps it non-crossing: the autosegmental analogue of
    `SimpleGraph.map` along a monotone vertex map. The upper index needs a
    `LinearOrder` (the run-collapse domain is `ℕ`) so that `ρ` reflects `<`. Used to
    lift planarity through the OCP run-collapse `ρ` (`Autosegmental/Collapse.lean`). -/
theorem IsNonCrossing.image_monotone (hρ : Monotone ρ) (h : IsNonCrossing links) :
    IsNonCrossing (links.image (Prod.map ρ id)) := by
  rw [isNonCrossing_image]; grind [IsNonCrossing, MonovaryOn, Monotone.reflect_lt]

end ImageMonotone

/-! ### The crossing relation and the GEN filter -/

section Candidate
variable [Preorder ι] [Preorder κ] [DecidableEq ι] [DecidableEq κ]
  {links : Finset (ι × κ)} {a b p : ι × κ}

/-- Two links **cross**: as a pair they fail to be non-crossing (equivalently their
    endpoints straddle in opposite tier- and backbone-order — `crosses_iff`). -/
def Crosses (a b : ι × κ) : Prop := ¬ IsNonCrossing {a, b}

/-- `p` crosses some link already in `links` — the decidable GEN filter. -/
def IndexCrosses (links : Finset (ι × κ)) (p : ι × κ) : Prop := ∃ l ∈ links, Crosses p l

instance [DecidableLT ι] [DecidableLE κ] : Decidable (Crosses a b) :=
  inferInstanceAs (Decidable (¬ IsNonCrossing {a, b}))

instance [DecidableLT ι] [DecidableLE κ] : Decidable (IndexCrosses links p) :=
  inferInstanceAs (Decidable (∃ l ∈ links, Crosses p l))

/-- Crossing is symmetric: `{a, b}` is the same pair as `{b, a}`. -/
theorem crosses_comm : Crosses a b ↔ Crosses b a := by rw [Crosses, Crosses, Finset.pair_comm]

/-- `p` crosses nothing iff it is pairwise non-crossing with every existing link. -/
theorem not_indexCrosses_iff :
    ¬ IndexCrosses links p ↔ ∀ l ∈ links, IsNonCrossing {p, l} := by
  simp only [IndexCrosses, Crosses, not_exists, not_and, not_not]

/-- Adding `p` keeps non-crossing iff it crosses no existing link: the GEN-filter
    form of `isNonCrossing_insert_iff`. -/
theorem isNonCrossing_insert_iff_not_indexCrosses :
    IsNonCrossing (insert p links) ↔ IsNonCrossing links ∧ ¬ IndexCrosses links p := by
  rw [isNonCrossing_insert_iff, not_indexCrosses_iff]

/-- GEN direction of `isNonCrossing_insert_iff_not_indexCrosses`. -/
theorem IsNonCrossing.insert_of_not_indexCrosses
    (hNC : IsNonCrossing links) (hNX : ¬ IndexCrosses links p) :
    IsNonCrossing (insert p links) :=
  isNonCrossing_insert_iff_not_indexCrosses.mpr ⟨hNC, hNX⟩

end Candidate

section CandidateLinear
variable [Preorder ι] [LinearOrder κ] [DecidableEq ι] [DecidableEq κ]
  {links : Finset (ι × κ)} {a b p : ι × κ}

/-- `Crosses` in elementary order form: one link's endpoints straddle the other's
    in opposite order. -/
theorem crosses_iff :
    Crosses a b ↔ (a.1 < b.1 ∧ b.2 < a.2) ∨ (b.1 < a.1 ∧ a.2 < b.2) := by
  rw [Crosses, isNonCrossing_pair]; grind

/-- `IndexCrosses` in elementary index-ordering form. -/
theorem indexCrosses_iff :
    IndexCrosses links p ↔
      ∃ l ∈ links, (p.1 < l.1 ∧ l.2 < p.2) ∨ (l.1 < p.1 ∧ p.2 < l.2) := by
  simp only [IndexCrosses, crosses_iff]

end CandidateLinear

/-! ### Link shift (the concatenation offset)

The coordinate offset that places a morpheme's links past the preceding tiers under
concatenation ([jardine-heinz-2015]). Shared by the bipartite `Graph` and the n-tier
`MultiGraph`, which apply it to their one / each tier-pair respectively. -/

/-- Shift a link's two endpoints by `(δ₁, δ₂)`. -/
def shiftLink (δ₁ δ₂ : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + δ₁, p.2 + δ₂)

@[simp] theorem shiftLink_apply (δ₁ δ₂ : ℕ) (p : ℕ × ℕ) :
    shiftLink δ₁ δ₂ p = (p.1 + δ₁, p.2 + δ₂) := rfl

@[simp] theorem shiftLink_zero : shiftLink 0 0 = (id : ℕ × ℕ → ℕ × ℕ) := by funext p; simp

theorem shiftLink_comp (a₁ a₂ b₁ b₂ : ℕ) :
    shiftLink a₁ a₂ ∘ shiftLink b₁ b₂ = shiftLink (a₁ + b₁) (a₂ + b₂) := by
  funext p; simp only [Function.comp_apply, shiftLink_apply, Prod.mk.injEq]; omega

/-- Shifting a link set preserves non-crossing: `shiftLink` is a coordinatewise
    order-embedding, so via `isNonCrossing_image` it preserves monovariance. -/
theorem isNonCrossing_image_shiftLink (s : Finset (ℕ × ℕ)) (δ₁ δ₂ : ℕ) :
    IsNonCrossing (s.image (shiftLink δ₁ δ₂)) ↔ IsNonCrossing s := by
  grind [isNonCrossing_image, IsNonCrossing, MonovaryOn, shiftLink]

end Autosegmental
