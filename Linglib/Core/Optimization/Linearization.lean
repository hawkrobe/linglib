/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Pareto dominance and positive linearizations

Pointwise (Pareto) dominance between `ℕ`-valued cost vectors over finitely many
dimensions is characterized by weighted sums: `f < g` pointwise iff every
strictly positive weighting ranks `∑ i, w i * f i` below `∑ i, w i * g i`.
Monotonicity of weighted sums gives one direction; a weighting concentrated on
a violating coordinate separates the other. Consequently two vectors are
incomparable iff two positive weightings disagree about them — the exact sense
in which a weighted-sum model can, and Pareto reasoning cannot, break ties.

Companion to `Core.Optimization.Pareto` (the pullback-preorder view of the
pointwise order); weighted aggregation itself stays in consuming layers
(`Core.Optimization.System`). `[UPSTREAM]` candidate: mathlib provides the
pointwise order and the engine `Finset.sum_lt_sum`, but not the
characterization; on upstreaming, generalize the codomain from `ℕ`.

## Main results

* `sum_mul_lt_sum_mul` — pointwise `≤` and strictness at one positively
  weighted coordinate give a strict weighted-sum inequality.
* `exists_pos_weight_sum_mul_lt` — a coordinate-wise strict inequality admits
  a strictly positive weighting whose weighted sums order strictly.
* `le_iff_forall_pos_weight`, `lt_iff_forall_pos_weight` — Pareto `≤` / `<`
  coincide with agreement of all strictly positive weightings.
* `exists_pos_weights_disagree` — incomparable vectors are ordered oppositely
  by two positive weightings.
-/

namespace Core.Optimization

variable {ι : Type*} [Fintype ι] {f g w : ι → ℕ}

/-- Weighted sums are monotone in the pointwise order. -/
theorem sum_mul_le_sum_mul (hle : f ≤ g) : ∑ i, w i * f i ≤ ∑ i, w i * g i :=
  Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hle i)

/-- Pointwise `≤` with strictness at a positively weighted coordinate gives a
    strict weighted-sum inequality. -/
theorem sum_mul_lt_sum_mul (hle : f ≤ g) (h : ∃ i, 0 < w i ∧ f i < g i) :
    ∑ i, w i * f i < ∑ i, w i * g i :=
  have ⟨i, hw, hi⟩ := h
  Finset.sum_lt_sum (fun j _ => Nat.mul_le_mul_left _ (hle j))
    ⟨i, Finset.mem_univ i, Nat.mul_lt_mul_of_pos_left hi hw⟩

/-- A coordinate-wise strict inequality admits a strictly positive weighting
    whose weighted sums order the vectors strictly: weight `∑ k, f k + 1` on
    the strict coordinate, `1` elsewhere. -/
theorem exists_pos_weight_sum_mul_lt (h : ∃ i, f i < g i) :
    ∃ w : ι → ℕ, (∀ j, 0 < w j) ∧ ∑ j, w j * f j < ∑ j, w j * g j := by
  classical
  obtain ⟨i, hi⟩ := h
  refine ⟨fun j => if j = i then (∑ k, f k) + 1 else 1,
    fun j => by dsimp only; split <;> omega, ?_⟩
  have hsplit : ∀ v : ι → ℕ,
      ∑ j, (if j = i then (∑ k, f k) + 1 else 1) * v j
        = ((∑ k, f k) + 1) * v i + ∑ j ∈ Finset.univ.erase i, v j := by
    intro v
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
    exact congrArg _ (Finset.sum_congr rfl fun j hj => by
      rw [if_neg (Finset.ne_of_mem_erase hj), one_mul])
  rw [hsplit f, hsplit g]
  calc ((∑ k, f k) + 1) * f i + ∑ j ∈ Finset.univ.erase i, f j
      ≤ ((∑ k, f k) + 1) * f i + ∑ k, f k :=
        Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)) _
    _ < ((∑ k, f k) + 1) * f i + ((∑ k, f k) + 1) :=
        Nat.add_lt_add_left (Nat.lt_succ_self _) _
    _ = ((∑ k, f k) + 1) * (f i + 1) := (Nat.mul_succ _ _).symm
    _ ≤ ((∑ k, f k) + 1) * g i := Nat.mul_le_mul_left _ hi
    _ ≤ ((∑ k, f k) + 1) * g i + ∑ j ∈ Finset.univ.erase i, g j := Nat.le_add_right _ _

/-- Pareto `≤` is agreement of every strictly positive weighting. -/
theorem le_iff_forall_pos_weight :
    f ≤ g ↔ ∀ w : ι → ℕ, (∀ i, 0 < w i) → ∑ i, w i * f i ≤ ∑ i, w i * g i := by
  refine ⟨fun h w _ => sum_mul_le_sum_mul h, fun h => ?_⟩
  by_contra hng
  obtain ⟨i, hi⟩ : ∃ i, g i < f i := by
    simpa [Pi.le_def, Nat.not_le] using hng
  obtain ⟨w, hw, hlt⟩ := exists_pos_weight_sum_mul_lt ⟨i, hi⟩
  exact absurd (h w hw) (Nat.not_le.mpr hlt)

/-- Pareto dominance is strict agreement of every strictly positive weighting. -/
theorem lt_iff_forall_pos_weight :
    f < g ↔ ∀ w : ι → ℕ, (∀ i, 0 < w i) → ∑ i, w i * f i < ∑ i, w i * g i := by
  constructor
  · intro h w hw
    obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp h
    obtain ⟨i, hi⟩ : ∃ i, f i < g i := by
      by_contra hno
      exact hne (funext fun i =>
        Nat.le_antisymm (hle i) (Nat.not_lt.mp (not_exists.mp hno i)))
    exact sum_mul_lt_sum_mul hle ⟨i, hw i, hi⟩
  · intro h
    have hle : f ≤ g := le_iff_forall_pos_weight.mpr fun w hw => (h w hw).le
    refine lt_of_le_of_ne hle fun heq => ?_
    exact absurd (h (fun _ => 1) fun _ => one_pos) (heq ▸ lt_irrefl _)

/-- Pareto-incomparable vectors are ordered oppositely by two strictly
    positive weightings: weighted-sum models can, and Pareto reasoning cannot,
    break the tie. -/
theorem exists_pos_weights_disagree (h₁ : ¬ f ≤ g) (h₂ : ¬ g ≤ f) :
    ∃ w w' : ι → ℕ, (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      ∑ i, w i * f i < ∑ i, w i * g i ∧ ∑ i, w' i * g i < ∑ i, w' i * f i := by
  obtain ⟨i, hi⟩ : ∃ i, f i < g i := by
    simpa [Pi.le_def, Nat.not_le] using h₂
  obtain ⟨j, hj⟩ : ∃ j, g j < f j := by
    simpa [Pi.le_def, Nat.not_le] using h₁
  obtain ⟨w, hw, hlt⟩ := exists_pos_weight_sum_mul_lt ⟨i, hi⟩
  obtain ⟨w', hw', hlt'⟩ := exists_pos_weight_sum_mul_lt ⟨j, hj⟩
  exact ⟨w, w', hw, hw', hlt, hlt'⟩

end Core.Optimization
