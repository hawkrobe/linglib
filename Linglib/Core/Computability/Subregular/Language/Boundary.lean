/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.List.Chain
import Linglib.Core.Data.List.Config
import Linglib.Core.Data.List.Factors

/-!
# Subregular Languages: Boundary Augmentation

Boundary augmentation of strings and a boundary-vacuity predicate relating the
chain-membership of a padded string to that of its unpadded core. The strictly-local,
locally-testable, and tier-relativized classes are built on this infrastructure
[lambert-2022] [heinz-rogers-2010] [rogers-pullum-2011]. The contiguous `k`-factors
the hierarchy quantifies over are a generic list combinator and live in
`Core/Data/List/Factors.lean` (`List.kFactors`).

## Main definitions

* `Subregular.Augmented α` — the boundary-augmented alphabet `List (Option α)`,
  with `none` the boundary marker.
* `Subregular.boundary k w` — `w` injected into `Augmented α` and padded with
  `k - 1` boundary markers on each side.
* `Subregular.IsBoundaryVacuous R` — `R` holds whenever either argument is the
  boundary marker `none`.

## Main results

* `Subregular.IsBoundaryVacuous.isChain_boundary_two_iff` — boundary padding does
  not change `IsChain`-membership for a boundary-vacuous relation.

## Implementation notes

The standard subregular convention extends the alphabet with two edge markers
`⋊`, `⋉` and studies the `k`-factors of `⋊ᵏ⁻¹ · w · ⋉ᵏ⁻¹`. We instead use the
one-fresh-symbol extension `Option α` (`none` = boundary, `some a` = original
symbol): a single marker suffices because boundary symbols only ever occur at
fixed positions, so the two edges are never confused.
-/

namespace Subregular

variable {α : Type*}

/-! ### Boundary augmentation -/

/-- The boundary-augmented alphabet: original symbols (`some a`) plus the
boundary marker `none`. -/
abbrev Augmented (α : Type*) := List (Option α)

section Boundary

variable (k : ℕ) (w : List α)

/-- `w` padded with `k - 1` boundary markers (`none`) on each side. -/
def boundary : Augmented α :=
  List.replicate (k - 1) none ++ w.map some ++ List.replicate (k - 1) none

@[simp] lemma boundary_one : boundary 1 w = w.map some := by
  simp [boundary]

lemma length_boundary : (boundary k w).length = w.length + 2 * (k - 1) := by
  simp [boundary]; omega

end Boundary

/-! ### Position discrimination and the configuration bridge

Entries of `boundary k y` are values of the word's two-sided configuration
(`List.config`), shifted by the pad width; consequently the `k`-factors of the
augmented word are exactly its windows (`List.window`). -/

section Pinning

variable {k : ℕ} {w y l : List α}

/-- The augmented string's entries by region: left pad, letters, right pad. -/
lemma getElem?_boundary (j : ℕ) :
    (boundary k w)[j]? =
      if j < k - 1 then some none
      else if j < k - 1 + w.length then (w[j - (k - 1)]?).map some
      else if j < w.length + 2 * (k - 1) then some none
      else none := by
  unfold boundary
  rcases lt_or_ge j (k - 1) with h1 | h1
  · rw [if_pos h1, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simpa using h1), List.getElem?_replicate, if_pos h1]
  rcases lt_or_ge j (k - 1 + w.length) with h2 | h2
  · rw [if_neg (by omega), if_pos h2, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simpa using h1), List.getElem?_map,
      List.length_replicate]
  rcases lt_or_ge j (w.length + 2 * (k - 1)) with h3 | h3
  · rw [if_neg (by omega), if_neg (by omega), if_pos h3,
      List.getElem?_append_right (by simp; omega), List.getElem?_replicate,
      if_pos (by simp; omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      List.getElem?_eq_none (by simp; omega)]

/-- A letter entry sits in the letter region. -/
lemma of_getElem?_boundary_eq_some {j : ℕ} {a : α}
    (h : (boundary k w)[j]? = some (some a)) :
    k - 1 ≤ j ∧ w[j - (k - 1)]? = some a := by
  rw [getElem?_boundary] at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by simp)
  · exact ⟨by omega, by simpa using h⟩
  · exact absurd h (by simp)

/-- A marker entry sits in one of the pads. -/
lemma of_getElem?_boundary_eq_none {j : ℕ}
    (h : (boundary k w)[j]? = some (none : Option α)) :
    j < k - 1 ∨ k - 1 + w.length ≤ j := by
  rw [getElem?_boundary] at h
  split_ifs at h with h1 h2 h3
  · exact .inl h1
  · exact absurd h (by simp)
  · exact .inr (by omega)

/-- Boundary entries are configuration values, shifted by the pad width. -/
lemma getElem?_boundary_eq_config {q : ℕ} (h : q < w.length + 2 * (k - 1)) :
    (boundary k w)[q]? = some (w.config ((q : ℤ) - (k - 1 : ℕ))) := by
  rw [getElem?_boundary]
  split_ifs with h1 h2
  · rw [List.config_neg (by omega)]
  · have hlt : q - (k - 1) < w.length := by omega
    rw [show ((q : ℤ) - (k - 1 : ℕ)) = ((q - (k - 1) : ℕ) : ℤ) by omega,
      List.config_natCast, List.getElem?_eq_getElem hlt, Option.map_some]
  · rw [List.config_eq_none_iff.mpr (.inr (by omega))]

/-- The `k`-factors of the augmented word are exactly its windows over
`[1 - k, w.length)`. -/
lemma mem_kFactors_boundary_iff {f : List (Option α)} (hk : 1 ≤ k) :
    f ∈ List.kFactors k (boundary k y) ↔
      ∃ i : ℤ, 1 - k ≤ i ∧ i < y.length ∧ f = List.window k y i := by
  rw [List.mem_kFactors]
  constructor
  · rintro ⟨hinf, hlen⟩
    obtain ⟨δ, hδ⟩ := (List.isInfix_iff_exists_offset _ _).mp hinf
    have hbound : δ + k ≤ y.length + 2 * (k - 1) := by
      by_contra hc
      have h1 := hδ (k - 1) (by omega)
      rw [List.getElem?_eq_none
        (show (boundary k y).length ≤ k - 1 + δ by rw [length_boundary]; omega)] at h1
      have h2 := List.getElem?_eq_none_iff.mp h1.symm
      omega
    refine ⟨(δ : ℤ) - (k - 1 : ℕ), by omega, by omega, ?_⟩
    apply List.ext_getElem?
    intro j
    rcases lt_or_ge j k with hj | hj
    · rw [List.getElem?_window hj]
      have h1 := (hδ j (by omega)).symm
      rw [getElem?_boundary_eq_config (q := j + δ) (by omega)] at h1
      rw [h1, show ((j + δ : ℕ) : ℤ) - ((k - 1 : ℕ) : ℤ) = (δ : ℤ) - (k - 1 : ℕ) + (j : ℕ)
        by omega]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hj)]
  · rintro ⟨i, h1, h2, rfl⟩
    refine ⟨(List.isInfix_iff_exists_offset _ _).mpr
      ⟨(i + (k - 1 : ℕ)).toNat, fun j hj => ?_⟩, by simp⟩
    rw [List.length_window] at hj
    rw [List.getElem?_window hj,
      getElem?_boundary_eq_config (q := j + (i + (k - 1 : ℕ)).toNat) (by omega),
      show ((j + (i + (k - 1 : ℕ)).toNat : ℕ) : ℤ) - ((k - 1 : ℕ) : ℤ) = i + (j : ℕ)
        by omega]

end Pinning

/-! ### Boundary-vacuous relations -/

/-- A relation on `Option α` is **boundary-vacuous** when `none` satisfies it on
either side (`R none u`, `R u none`) — so only `(some a, some b)` pairs can
witness a violation. Subregular edge constraints (OCP, no-clash, no-lapse) all
share this shape. -/
structure IsBoundaryVacuous (R : Option α → Option α → Prop) : Prop where
  none_left : ∀ u, R none u
  none_right : ∀ u, R u none

namespace IsBoundaryVacuous

variable {R : Option α → Option α → Prop}

/-- 2-boundary padding preserves `IsChain` for a boundary-vacuous relation. -/
lemma isChain_boundary_two_iff (hR : IsBoundaryVacuous R) (ys : List α) :
    (boundary 2 ys).IsChain R ↔ (ys.map some).IsChain R := by
  show (none :: (ys.map some ++ [none])).IsChain R ↔ _
  rw [List.isChain_cons_iff_of_forall_rel hR.none_left,
      List.isChain_append_singleton_iff_of_forall_rel hR.none_right]

end IsBoundaryVacuous

end Subregular
