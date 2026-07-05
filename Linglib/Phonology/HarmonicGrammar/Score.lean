/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Constraints.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Harmony: evaluation and dominance lemmas

The reusable lemma layer over `harmonyScore`/`weightedViolations`
(`Constraints.Defs`), shaped so Harmonic-Grammar study files reason about
concrete grammars without hand-unfolding `Finset.sum`.

## Main results

* `harmonyScore_cons` / `harmonyScore_nil`, `weightedViolations_cons` /
  `weightedViolations_nil` — `@[simp]` cons-recursion that evaluates harmony on a
  literal grammar `![C₀, …]` / `![w₀, …]` (fires only on `Matrix.vecCons`, so it is
  inert on abstract `con`/`w`).
* `harmonyScore_le_of_forall_le`, `harmonyDominates_of_lt` — **harmonic bounding**:
  a candidate with pointwise-fewer violations under non-negative weights has at
  least (resp. strictly greater) harmony. The Pareto argument most HG studies make,
  stated directly over the violation profile rather than via the weighted sum.
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
  simp [harmonyScore, weightedViolations]

@[simp] theorem harmonyScore_cons (c₀ : Constraint C) (con : CON C n)
    (w₀ : ℝ) (w : Fin n → ℝ) (x : C) :
    harmonyScore (Matrix.vecCons c₀ con) (Matrix.vecCons w₀ w) x =
      -(w₀ * (c₀ x : ℝ)) + harmonyScore con w x := by
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum, Fin.sum_univ_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-! ### Harmonic bounding (Pareto dominance) -/

variable {con : CON C n} {w : Fin n → ℝ} {a b : C}

/-- **Harmonic bounding (weak)**: with non-negative weights, a candidate `a`
that incurs no more violations than `b` on every constraint has at least `b`'s
harmony. The monotone core of OT's harmonic-bounding argument. -/
theorem harmonyScore_le_of_forall_le (hw : ∀ i, 0 ≤ w i)
    (h : ∀ i, con i a ≤ con i b) :
    harmonyScore con w b ≤ harmonyScore con w a := by
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum, neg_le_neg_iff]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast h i) (hw i)

/-- **Harmonic bounding (strict)**: with non-negative weights, if `a` incurs no
more violations than `b` everywhere and strictly fewer on some positively-weighted
constraint, then `a` strictly dominates `b` in harmony. Lets a study conclude
`harmonyDominates con w a b` from a violation-profile comparison alone. -/
theorem harmonyDominates_of_lt (hw : ∀ i, 0 ≤ w i)
    (hle : ∀ i, con i a ≤ con i b)
    (hlt : ∃ i, 0 < w i ∧ con i a < con i b) :
    harmonyDominates con w a b := by
  rw [harmonyDominates_iff, harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum,
    neg_lt_neg_iff]
  obtain ⟨j, hwj, hvj⟩ := hlt
  refine Finset.sum_lt_sum (fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hle i) (hw i)) ⟨j, Finset.mem_univ j, ?_⟩
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hvj) hwj

end Constraints
