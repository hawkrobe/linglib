/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.List.Chain
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

/-! ### Position discrimination and pinning

An infix of `boundary k y` that shows a boundary marker is *anchored*: a marker
followed by letters pins them to the start of `y`, letters followed by a marker pin
them to the end, and an all-letter infix reflects to an infix of `y`. -/

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

private lemma letters_of_offset {δ : ℕ}
    (hδ : ∀ i (_ : i < 1 + l.length),
      (boundary k y)[i + δ]? = ([none] ++ l.map some)[i]?) :
    ∀ i (_ : i < l.length), (boundary k y)[1 + i + δ]? = some (some l[i]) :=
  fun i hilt => by
    have := hδ (1 + i) (by omega)
    rwa [List.getElem?_append_right (by simp), List.length_singleton,
      Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem hilt,
      Option.map_some] at this

/-- Letters right after a boundary marker are word-initial. -/
lemma prefix_of_boundary_infix (hl : l ≠ [])
    (h : ([none] ++ l.map some) <:+: boundary k y) : l <+: y := by
  obtain ⟨δ, hδ⟩ := (List.isInfix_iff_exists_offset _ _).mp h
  have hi := letters_of_offset (l := l) fun i hi => hδ i (by simp; omega)
  have h0 : (boundary k y)[δ]? = some none := by simpa using hδ 0 (by simp)
  have hpos := List.length_pos_of_ne_nil hl
  obtain ⟨hk1, hy0⟩ := of_getElem?_boundary_eq_some (hi 0 hpos)
  have hpin : 1 + δ = k - 1 := by
    rcases of_getElem?_boundary_eq_none h0 with hlt | hge
    · omega
    · have := (List.getElem?_eq_some_iff.mp hy0).1
      omega
  have hylen : ∀ i (_ : i < l.length), y[i]? = some l[i] := fun i hilt => by
    have := (of_getElem?_boundary_eq_some (hi i hilt)).2
    rwa [show 1 + i + δ - (k - 1) = i by omega] at this
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  rcases lt_or_ge i l.length with hilt | hile
  · rw [List.getElem?_take_of_lt hilt, hylen i hilt, List.getElem?_eq_getElem hilt]
  · rw [List.getElem?_take_eq_none hile, List.getElem?_eq_none hile]

/-- Letters right before a boundary marker are word-final. -/
lemma suffix_of_boundary_infix (hl : l ≠ [])
    (h : (l.map some ++ [none]) <:+: boundary k y) : l <:+ y := by
  obtain ⟨δ, hδ⟩ := (List.isInfix_iff_exists_offset _ _).mp h
  have hi : ∀ i (_ : i < l.length), (boundary k y)[i + δ]? = some (some l[i]) :=
    fun i hilt => by
      have := hδ i (by simp; omega)
      rwa [List.getElem?_append_left (by simpa using hilt), List.getElem?_map,
        List.getElem?_eq_getElem hilt, Option.map_some] at this
  have hnone : (boundary k y)[l.length + δ]? = some none := by
    have := hδ l.length (by simp)
    rw [List.getElem?_append_right (by simp)] at this
    simpa using this
  have hpos := List.length_pos_of_ne_nil hl
  obtain ⟨hk0, -⟩ := of_getElem?_boundary_eq_some (hi 0 hpos)
  have hbounds : ∀ i (_ : i < l.length), i + δ - (k - 1) < y.length := fun i hilt =>
    (List.getElem?_eq_some_iff.mp (of_getElem?_boundary_eq_some (hi i hilt)).2).1
  have hpin : l.length + δ = k - 1 + y.length := by
    rcases of_getElem?_boundary_eq_none hnone with hlt | hge
    · omega
    · have := hbounds (l.length - 1) (by omega)
      omega
  have hly : l.length ≤ y.length := by
    have := hbounds 0 hpos
    omega
  have hylen : ∀ i (_ : i < l.length), y[y.length - l.length + i]? = some l[i] :=
    fun i hilt => by
      have := (of_getElem?_boundary_eq_some (hi i hilt)).2
      rwa [show i + δ - (k - 1) = y.length - l.length + i by omega] at this
  rw [List.suffix_iff_eq_drop]
  apply List.ext_getElem?
  intro i
  rcases lt_or_ge i l.length with hilt | hile
  · rw [List.getElem?_drop, hylen i hilt, List.getElem?_eq_getElem hilt]
  · rw [List.getElem?_eq_none hile, List.getElem?_eq_none (by simp; omega)]

/-- An all-letter infix reflects to an infix of the word. -/
lemma infix_of_boundary_infix (h : l.map some <:+: boundary k y) : l <:+: y := by
  rcases eq_or_ne l [] with rfl | hl
  · exact List.nil_infix
  obtain ⟨δ, hδ⟩ := (List.isInfix_iff_exists_offset _ _).mp h
  have hi : ∀ i (_ : i < l.length), (boundary k y)[i + δ]? = some (some l[i]) :=
    fun i hilt => by
      have := hδ i (by simpa using hilt)
      rwa [List.getElem?_map, List.getElem?_eq_getElem hilt, Option.map_some] at this
  have hk0 := (of_getElem?_boundary_eq_some (hi 0 (List.length_pos_of_ne_nil hl))).1
  refine (List.isInfix_iff_exists_offset _ _).mpr ⟨δ - (k - 1), fun i hilt => ?_⟩
  have := (of_getElem?_boundary_eq_some (hi i hilt)).2
  rw [show i + δ - (k - 1) = i + (δ - (k - 1)) by omega] at this
  rw [this, List.getElem?_eq_getElem hilt]

/-- Letters flanked by boundary markers on both sides are the whole word. -/
lemma eq_of_boundary_infix (hl : l ≠ [])
    (h : ([none] ++ l.map some ++ [none]) <:+: boundary k y) : y = l := by
  have hpre : l <+: y :=
    prefix_of_boundary_infix hl ((List.prefix_append _ _).isInfix.trans h)
  obtain ⟨δ, hδ⟩ := (List.isInfix_iff_exists_offset _ _).mp h
  have hi := letters_of_offset (l := l) fun i hi => by
    have := hδ i (by simp; omega)
    rwa [List.getElem?_append_left (by simp; omega)] at this
  have h0 : (boundary k y)[δ]? = some none := by
    have := hδ 0 (by simp)
    simpa using this
  have hpos := List.length_pos_of_ne_nil hl
  obtain ⟨hk1, hy0⟩ := of_getElem?_boundary_eq_some (hi 0 hpos)
  have hpin : 1 + δ = k - 1 := by
    rcases of_getElem?_boundary_eq_none h0 with hlt | hge
    · omega
    · have := (List.getElem?_eq_some_iff.mp hy0).1
      omega
  have hlast : (boundary k y)[1 + l.length + δ]? = some none := by
    have h' := hδ (1 + l.length)
      (by simp only [List.length_append, List.length_map, List.length_singleton]; omega)
    rwa [show ([none] ++ l.map some ++ [none] : List (Option α))[1 + l.length]?
        = some none by
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_map, List.length_singleton]
      rw [show 1 + l.length - (1 + l.length) = 0 by omega]
      rfl] at h'
  have hyle : y.length ≤ l.length := by
    rcases of_getElem?_boundary_eq_none hlast with hlt | hge
    · omega
    · omega
  exact (hpre.eq_of_length (le_antisymm hpre.length_le hyle)).symm

/-- A boundary-only infix of full width forces the empty word. -/
lemma eq_nil_of_boundary_infix (hk : 2 ≤ k)
    (h : List.replicate k (none : Option α) <:+: boundary k y) : y = [] := by
  obtain ⟨δ, hδ⟩ := (List.isInfix_iff_exists_offset _ _).mp h
  have hi : ∀ i (_ : i < k), (boundary k y)[i + δ]? = some none := fun i hilt => by
    have := hδ i (by simpa using hilt)
    rwa [List.getElem?_replicate, if_pos hilt] at this
  rcases of_getElem?_boundary_eq_none (hi 0 (by omega)) with hlt | hge
  · have := of_getElem?_boundary_eq_none (hi (k - 1 - δ) (by omega))
    rw [show k - 1 - δ + δ = k - 1 by omega] at this
    rcases this with h' | h'
    · omega
    · exact List.length_eq_zero_iff.mp (by omega)
  · have := (List.getElem?_eq_some_iff.mp (hi (k - 1) (by omega))).1
    rw [length_boundary] at this
    omega

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
