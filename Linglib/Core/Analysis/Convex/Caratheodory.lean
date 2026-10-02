module

public import Mathlib.Analysis.Convex.Caratheodory

/-!
# Carathéodory's theorem with finset weights

`[UPSTREAM]` A point in the convex hull of a set `s` is a convex combination, with strictly
positive weights, of an affinely independent finset of points of `s`. This is the `Finset` form
of `eq_pos_convex_span_of_mem_convexHull`, which indexes the points by an existentially
quantified type. In dimension `d` such a finset has at most `d + 1` points
(`AffineIndependent.finset_card_le_finrank_succ`).

## Tags

convex hull, caratheodory
-/

@[expose] public section

open Finset

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s : Set E} {x : E}

/-- **Carathéodory's convexity theorem** in explicit `Finset` form. A point in the convex hull of
`s` is a convex combination, with strictly positive weights, of an affinely independent finset of
points of `s`. -/
theorem exists_finset_eq_pos_convex_span_of_mem_convexHull (hx : x ∈ convexHull 𝕜 s) :
    ∃ t : Finset E, ↑t ⊆ s ∧ AffineIndependent 𝕜 ((↑) : t → E) ∧ ∃ w : E → 𝕜,
      (∀ y ∈ t, 0 < w y) ∧ ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = x := by
  classical
  rw [convexHull_eq_union] at hx
  obtain ⟨t, hts, hti, hxt⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
  obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.1 hxt
  have hw (y) (hy : y ∈ t) (h : w y ≠ 0) : 0 < w y := (hw₀ y hy).lt_of_ne' h
  refine ⟨{y ∈ t | 0 < w y}, fun y hy ↦ hts (mem_filter.1 hy).1,
    hti.mono (coe_subset.2 (filter_subset _ _)), w, fun y hy ↦ (mem_filter.1 hy).2, ?_, ?_⟩
  · rwa [sum_filter_of_ne hw]
  · rwa [sum_filter_of_ne fun y hy h ↦ hw y hy (left_ne_zero_of_smul h)]
