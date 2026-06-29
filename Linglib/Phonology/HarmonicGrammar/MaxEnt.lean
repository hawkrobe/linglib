import Linglib.Phonology.Constraints.Defs
import Linglib.Core.Probability.CoupledEvaluation

/-!
# MaxEnt Constraint Systems [storme-2026]

MaxEnt grammars assign probabilities to input→output mappings using the
softmax function over weighted constraint violations — the probabilistic
generalization of OT (where α → ∞ recovers categorical optimization;
see `softmax_argmax_limit`).

This module extends the basic MaxEnt setup with **systemic constraints**
([storme-2026]): constraints that evaluate *tuples* of mappings jointly
(e.g., \*HOMOPHONY penalizes distinct inputs that map to the same output).
Systemic constraints require evaluating a joint distribution over the product
space of all input→output mappings, then marginalizing to recover individual
mapping probabilities.

The framework is generic in the candidate type — phonology is one
instance, but the same machinery applies to any domain that scores
candidates by weighted constraint violations.

## Architecture

- A classical MaxEnt grammar is a constraint set `con : CON (I × O) n` + weight
  vector `w` (from `Constraints.Defs`), realized as a `ConstraintSystem` via
  `CON.hgSystem`; its probability is `predict` (no grammar record).
- `SystemicConstraint` evaluates *tuples* of outputs (different type signature)
- `jointHarmonyScore` combines classical + systemic scores over the product space
- `marginalProb` marginalizes the joint to recover individual mapping probabilities

## Key theorem

`marginal_eq_classical_when_no_systemic`: when systemic constraint weight = 0,
the marginalized probability equals classical MaxEnt. This is because the joint
score decomposes additively ⇒ the joint distribution factorizes ⇒ each marginal
equals its factor.
-/

namespace HarmonicGrammar

open Constraints Core

-- ============================================================================
-- § 1: Classical MaxEnt
-- ============================================================================

/-! Classical MaxEnt assigns `P(o ∣ i) ∝ exp(-harmonyScore con w (i, o))`. There is
**no grammar record**: a MaxEnt grammar is a constraint set `con : CON (I × O) n`
and a weight vector `w : Fin n → ℝ` held as plain values (the HG twin of an OT
`Ranking`), and its probability *is* `(CON.hgSystem con w Finset.univ).predict` —
softmax-decoded harmony, via the shared `Core.Optimization.ConstraintSystem`
(`CON.hgSystem` below). The systemic extension (§2–4) scores output *tuples*
jointly and so does not factor through the per-mapping `predict`. -/

-- ============================================================================
-- § 2: Systemic Constraints
-- ============================================================================

/-- A systemic constraint evaluates a *tuple* of outputs — one per input —
    rather than individual input→output pairs.

    Example: \*HOMOPHONY counts pairs of distinct inputs that map to the same
    output. This cannot be decomposed into per-mapping evaluations.

    `n` is the number of inputs; the tuple `Fin n → O` assigns an output
    to each input index. -/
structure SystemicConstraint (n : Nat) (O : Type*) where
  /-- Constraint name. -/
  name : String
  /-- Constraint weight. -/
  weight : ℝ
  /-- Evaluation function: how many violations does this output tuple incur? -/
  eval : (Fin n → O) → Nat

/-- \*HOMOPHONY: penalizes output tuples where distinct inputs receive the
    same output. Counts the number of colliding pairs.

    For n inputs, evaluates `|{(i,j) : i < j ∧ f(i) = f(j)}|`. -/
def homophonyAvoidance {n : Nat} {O : Type*} [DecidableEq O]
    (w : ℝ) : SystemicConstraint n O where
  name := "*HOMOPHONY"
  weight := w
  eval := λ f =>
    let pairs := do
      let i ← (List.finRange n)
      let j ← (List.finRange n)
      if i < j && f i == f j then [1] else []
    pairs.length

-- ============================================================================
-- § 3: Joint Distribution with Systemic Constraints
-- ============================================================================

/-- Systemic constraint score for an output tuple.
    This is the coupling component: `Σₖ (-wₖ · Sₖ(f))`. -/
def systemicScore {n : Nat} {O : Type*}
    (systemicConstraints : List (SystemicConstraint n O))
    (f : Fin n → O) : ℝ :=
  systemicConstraints.foldl (λ acc sc => acc - sc.weight * (sc.eval f : ℝ)) 0

/-- Joint harmony score over the product space.
    Combines classical per-mapping scores with systemic tuple-level scores.

    H_joint(f) = Σᵢ H_classical(iᵢ, f(i)) + Σₖ (-wₖ · Sₖ(f))

    where `f : Fin n → O` is the full output tuple. -/
noncomputable def jointHarmonyScore {n m : Nat} {I O : Type*}
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (systemicConstraints : List (SystemicConstraint n O))
    (f : Fin n → O) : ℝ :=
  let classical := (List.finRange n).foldl
    (λ acc i => acc + harmonyScore classicalCon classicalW (inputs i, f i)) 0
  classical + systemicScore systemicConstraints f

/-- MaxEnt grammar with systemic constraints as a `CoupledSoftmax`.

    - `componentScore i v = harmonyScore(classicalConstraints, (inputs i, v))`
    - `couplingScore f = systemicScore(systemicConstraints, f)`

    The joint probability is `softmax(totalScore, 1)` over all `Fin n → O`
    output tuples. The marginal at position `i` recovers the individual
    mapping probability under systemic pressure. -/
noncomputable def maxEntCoupled {n m : Nat} {I O : Type*} [Fintype O] [DecidableEq O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (systemicConstraints : List (SystemicConstraint n O)) :
    Core.CoupledSoftmax (Fin n) O :=
  Core.coupledSoftmaxOfMaxEnt inputs
    (fun p => harmonyScore classicalCon classicalW p)
    (fun f => systemicScore systemicConstraints f)

/-- Marginal probability: marginalize the joint distribution to get
    the probability of a specific input→output mapping.

    P_marginal(oᵢ | iᵢ) = Σ_{f : f(i) = oᵢ} P_joint(f)

    This is Storme's key equation: the marginal recovers individual mapping
    probabilities that reflect systemic pressure. Defined through
    `CoupledSoftmax.marginal` so that factorization follows from
    `marginal_eq_independent_when_uncoupled`. -/
noncomputable def marginalProb {n m : Nat} {I O : Type*} [Fintype O] [DecidableEq O]
    [Nonempty O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (systemicConstraints : List (SystemicConstraint n O))
    (i : Fin n) (o : O) : ℝ :=
  (maxEntCoupled inputs classicalCon classicalW systemicConstraints).marginal i o

-- ============================================================================
-- § 4: Factorization Theorem
-- ============================================================================

/-- When all systemic constraint weights are zero, the systemic score
    is zero for every output tuple. -/
private lemma systemicScore_zero {n : Nat} {O : Type*}
    {systemicConstraints : List (SystemicConstraint n O)}
    (h_zero : ∀ sc ∈ systemicConstraints, sc.weight = 0)
    (f : Fin n → O) :
    systemicScore systemicConstraints f = 0 := by
  induction systemicConstraints with
  | nil => rfl
  | cons sc rest ih =>
    simp only [systemicScore, List.foldl_cons]
    have hw : sc.weight = 0 := h_zero sc (.head _)
    rw [hw, zero_mul, sub_zero]
    exact ih (fun sc' hsc' => h_zero sc' (.tail _ hsc'))

/-- **Factorization**: when systemic constraint weights are all zero,
    the marginal equals the classical MaxEnt probability.

    With zero systemic weights, the coupling score is constant (= 0),
    so `marginal_eq_independent_when_uncoupled` applies: the joint
    factorizes and each marginal equals its independent per-item softmax. -/
theorem marginal_eq_classical_when_no_systemic {n m : Nat} {I O : Type*}
    [Fintype O] [DecidableEq O] [Nonempty O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (systemicConstraints : List (SystemicConstraint n O))
    (h_zero : ∀ sc ∈ systemicConstraints, sc.weight = 0)
    (i : Fin n) (o : O) :
    marginalProb inputs classicalCon classicalW systemicConstraints i o =
    softmax (λ o' => harmonyScore classicalCon classicalW (inputs i, o')) o :=
  (maxEntCoupled inputs classicalCon classicalW systemicConstraints).marginal_eq_independent_when_uncoupled
    ⟨0, systemicScore_zero h_zero⟩ i o

end HarmonicGrammar
