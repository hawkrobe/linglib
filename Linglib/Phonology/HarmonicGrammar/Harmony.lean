/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Linglib.Core.LinearAlgebra.Matrix.DotProduct

/-!
# Harmony

A Harmonic Grammar ([smolensky-legendre-2006]) weights each constraint of a constraint set `CON`
by a number, real in the usual statement, and the harmony of a candidate is the negated weighted
sum of its violations, `H(c) = -Σⱼ wⱼ · Cⱼ(c)`, a linear functional of the candidate's violation
vector. The weight vector `w : Fin n → R` is the grammar's parameter, the Harmonic-Grammar twin of
an OT `Ranking n`, and both act on one `CON`. The weight ring is a parameter so that a grammar with
rational or integer weights keeps its scores exactly computable.

Harmony is additive over concatenated and jointly evaluated constraint sets, so constraint
summation is innocuous for it, and with non-negative weights a candidate that incurs no more
violations than another on every constraint has at least its harmony, which is harmonic bounding.

## Main definitions

* `weightedViolations`: the weighted sum `Σⱼ wⱼ · vⱼ` of a violation vector.
* `harmonyScore`: the harmony `H(c) = -Σⱼ wⱼ · Cⱼ(c)` of a candidate.
* `harmonyDominates`: harmonic dominance, `H(a) > H(b)`.

## Main results

* `weightedViolations_cons`, `harmonyScore_cons`: `@[simp]` cons-recursion evaluating harmony on
  literal grammars `![C₀, …]`, `![w₀, …]`.
* `harmonyScore_congr`: harmony depends only on the violation profile.
* `harmonyScore_append`, `harmonyScore_joint`: harmony is additive over a concatenated constraint
  set and, for a jointly evaluated one, over the mappings.
* `weightedViolations_mono`: for `0 ≤ w`, the weighted violation sum is monotone in the violation
  profile.
* `harmonyScore_le_of_forall_le`, `harmonyDominates_of_lt`: a Pareto-dominant candidate has at
  least, and given a strict advantage on a positively weighted constraint strictly greater,
  harmony.

## References

* [P. Smolensky and G. Legendre, *The Harmonic Mind: From Neural Computation to
  Optimality-Theoretic Grammar* (2006)][smolensky-legendre-2006]
* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative Grammar*
  (1993)][prince-smolensky-1993]
* [G. Magri and B. Storme, *Constraint Summation in Phonological Theory* (2021)][magri-storme-2021]
-/

@[expose] public section

namespace HarmonicGrammar

open OptimalityTheory

variable {C : Type*} {n : ℕ} {R : Type*}

/-! ### Weighted violations and harmony -/

/-- The **weighted violation sum** of a violation vector `v` under a weight vector `w` is the
linear functional `Σⱼ wⱼ · vⱼ`. Harmony is its negation (`harmonyScore`). -/
def weightedViolations [Semiring R] (w : Fin n → R) (v : Fin n → ℕ) : R :=
  ∑ j, w j * (v j : R)

/-- The **harmony** `H(c) = -Σⱼ wⱼ · Cⱼ(c)` of a candidate ([smolensky-legendre-2006]) is the
negated weighted sum of its violations under the weight vector `w`, and higher harmony is more
grammatical. -/
def harmonyScore [Ring R] (con : CON C n) (w : Fin n → R) (c : C) : R :=
  -weightedViolations w (fun j ↦ con j c)

/-- `harmonyScore` is a negated `Finset.sum`. -/
theorem harmonyScore_eq_neg_sum [Ring R] (con : CON C n) (w : Fin n → R) (c : C) :
    harmonyScore con w c = -∑ j, w j * (con j c : R) := rfl

/-- The candidate `a` harmonically dominates `b` when `H(a) > H(b)`. The relation is the
pullback of `>` along `harmonyScore con w` (`Order.Preimage`), so it inherits `IsStrictOrder`
from the weight ring. -/
def harmonyDominates [Ring R] [LT R] (con : CON C n) (w : Fin n → R) : C → C → Prop :=
  harmonyScore con w ⁻¹'o (· > ·)

@[simp] theorem harmonyDominates_iff [Ring R] [LT R] (con : CON C n) (w : Fin n → R)
    (a b : C) : harmonyDominates con w a b ↔ harmonyScore con w b < harmonyScore con w a :=
  Iff.rfl

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

@[simp] theorem harmonyScore_zero_weight (con : CON C n) (x : C) :
    harmonyScore con (0 : Fin n → ℝ) x = 0 := by
  simp [harmonyScore, weightedViolations]

/-- Harmony depends only on the violation profile. -/
theorem harmonyScore_congr {con : CON C n} {w : Fin n → ℝ} {a b : C}
    (h : ∀ j, con j a = con j b) : harmonyScore con w a = harmonyScore con w b := by
  simp [harmonyScore, weightedViolations, h]

/-! ### Concatenated and jointly evaluated constraint sets -/

/-- Harmony is additive over a concatenated constraint set and weight vector. -/
theorem harmonyScore_append {m : ℕ} (c₁ : CON C n) (c₂ : CON C m) (w₁ : Fin n → ℝ)
    (w₂ : Fin m → ℝ) (x : C) :
    harmonyScore (Fin.append c₁ c₂) (Fin.append w₁ w₂) x =
      harmonyScore c₁ w₁ x + harmonyScore c₂ w₂ x := by
  simp [harmonyScore, weightedViolations, Fin.sum_univ_add, add_comm]

/-- The harmony of a jointly evaluated constraint set is the sum of the mappings'
harmonies — constraint summation is innocuous for harmony ([magri-storme-2021]). -/
theorem harmonyScore_joint {ι I O : Type*} [Fintype ι] (inputs : ι → I)
    (con : CON (I × O) n) (w : Fin n → ℝ) (f : ι → O) :
    harmonyScore (con.joint inputs) w f = ∑ i, harmonyScore con w (inputs i, f i) := by
  simp only [harmonyScore, weightedViolations, CON.joint_apply, Constraint.joint_apply,
    Nat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

/-! ### Harmonic bounding (Pareto dominance) -/

variable {con : CON C n} {w : Fin n → ℝ} {a b : C}

/-- For non-negative weights, the weighted violation sum is monotone in the
violation profile. -/
theorem weightedViolations_mono (hw : 0 ≤ w) : Monotone (weightedViolations w) :=
  fun _ _ h => dotProduct_le_dotProduct_of_nonneg_left (fun i => Nat.cast_le.2 (h i)) hw

/-- Pointwise `≤` with a strict advantage on a positively weighted coordinate
gives a strictly smaller weighted violation sum. -/
theorem weightedViolations_lt_weightedViolations {va vb : Fin n → ℕ} (hw : 0 ≤ w)
    (hle : va ≤ vb) (hlt : ∃ i, 0 < w i ∧ va i < vb i) :
    weightedViolations w va < weightedViolations w vb :=
  dotProduct_lt_dotProduct_of_nonneg_left (fun i => Nat.cast_le.2 (hle i)) hw
    (hlt.imp fun _ h => ⟨h.1, Nat.cast_lt.2 h.2⟩)

/-- With non-negative weights, a candidate incurring no more violations than `b` on every
constraint has at least `b`'s harmony, which is harmonic bounding ([prince-smolensky-1993]). -/
theorem harmonyScore_le_of_forall_le (hw : 0 ≤ w) (h : ∀ i, con i a ≤ con i b) :
    harmonyScore con w b ≤ harmonyScore con w a :=
  neg_le_neg (weightedViolations_mono hw h)

/-- Strictly fewer violations on some positively weighted constraint give strictly greater
harmony. -/
theorem harmonyDominates_of_lt (hw : 0 ≤ w) (hle : ∀ i, con i a ≤ con i b)
    (hlt : ∃ i, 0 < w i ∧ con i a < con i b) :
    harmonyDominates con w a b :=
  neg_lt_neg (weightedViolations_lt_weightedViolations hw hle hlt)

end HarmonicGrammar
