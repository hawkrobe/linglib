/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Harmony evaluation

Evaluation and order lemmas for `Constraints.harmonyScore` and
`Constraints.weightedViolations`.

## Main results

* `weightedViolations_cons`, `harmonyScore_cons`: `@[simp]` cons-recursion
  evaluating harmony on literal grammars `![C₀, …]`, `![w₀, …]`.
* `weightedViolations_mono`: for `0 ≤ w`, the weighted violation sum is
  monotone in the violation profile.
* `harmonyScore_le_of_forall_le`, `harmonyDominates_of_lt`: *harmonic
  bounding* — a Pareto-dominant candidate has at least, and given a strict
  advantage on a positively weighted constraint strictly greater, harmony
  ([prince-smolensky-1993]).
-/

namespace Constraints

variable {C : Type*} {n : ℕ}

/-! ### Evaluation by cons-recursion -/

@[simp] theorem weightedViolations_nil (w : Fin 0 → ℝ) (v : Fin 0 → ℕ) :
    weightedViolations w v = 0 := by
  simp [weightedViolations]

@[simp] theorem weightedViolations_cons (w₀ : ℝ) (w : Fin n → ℝ) (v₀ : ℕ) (v : Fin n → ℕ) :
    weightedViolations (Matrix.vecCons w₀ w) (Matrix.vecCons v₀ v) =
      w₀ * (v₀ : ℝ) + weightedViolations w v := by
  simp [weightedViolations, Fin.sum_univ_succ]

@[simp] theorem harmonyScore_nil (con : CON C 0) (w : Fin 0 → ℝ) (x : C) :
    harmonyScore con w x = 0 := by
  rw [harmonyScore, weightedViolations_nil, neg_zero]

@[simp] theorem harmonyScore_cons (c₀ : Constraint C) (con : CON C n)
    (w₀ : ℝ) (w : Fin n → ℝ) (x : C) :
    harmonyScore (Matrix.vecCons c₀ con) (Matrix.vecCons w₀ w) x =
      -(w₀ * (c₀ x : ℝ)) + harmonyScore con w x := by
  have h : (fun j => Matrix.vecCons c₀ con j x) = Matrix.vecCons (c₀ x) fun j => con j x :=
    funext (Fin.cases rfl fun _ => rfl)
  rw [harmonyScore, h, weightedViolations_cons, neg_add, harmonyScore]

/-! ### Harmonic bounding (Pareto dominance) -/

variable {con : CON C n} {w : Fin n → ℝ} {a b : C}

/-- For non-negative weights, the weighted violation sum is monotone in the
violation profile. -/
theorem weightedViolations_mono (hw : 0 ≤ w) : Monotone (weightedViolations w) :=
  fun _ _ h => Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast h i) (hw i)

/-- Pointwise `≤` with a strict advantage on a positively weighted coordinate
gives a strictly smaller weighted violation sum. -/
theorem weightedViolations_lt_weightedViolations {va vb : Fin n → ℕ} (hw : 0 ≤ w)
    (hle : va ≤ vb) (hlt : ∃ i, 0 < w i ∧ va i < vb i) :
    weightedViolations w va < weightedViolations w vb := by
  obtain ⟨j, hwj, hvj⟩ := hlt
  exact Finset.sum_lt_sum
    (fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast hle i) (hw i))
    ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left (by exact_mod_cast hvj) hwj⟩

/-- Harmonic bounding: with non-negative weights, a candidate incurring no more
violations than `b` on every constraint has at least `b`'s harmony
([prince-smolensky-1993]). -/
theorem harmonyScore_le_of_forall_le (hw : 0 ≤ w) (h : ∀ i, con i a ≤ con i b) :
    harmonyScore con w b ≤ harmonyScore con w a :=
  neg_le_neg (weightedViolations_mono hw h)

/-- Strict harmonic bounding: strictly fewer violations on some positively
weighted constraint gives strictly greater harmony. -/
theorem harmonyDominates_of_lt (hw : 0 ≤ w) (hle : ∀ i, con i a ≤ con i b)
    (hlt : ∃ i, 0 < w i ∧ con i a < con i b) :
    harmonyDominates con w a b :=
  neg_lt_neg (weightedViolations_lt_weightedViolations hw hle hlt)

end Constraints
