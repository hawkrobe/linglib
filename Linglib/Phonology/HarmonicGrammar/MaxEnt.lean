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
- `SystemicConstraint n O := (Fin n → O) → ℕ` scores a whole output *tuple* (the
  systemic twin of `Constraint`); weights are a separate `Fin k → ℝ` vector —
  no grammar record, mirroring the classical `con`/`w` split
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

/-- A **systemic constraint** evaluates a whole output *tuple* — one output per
    input — rather than an individual input→output pair, so it cannot be
    decomposed into per-mapping evaluations (e.g. \*HOMOPHONY counts colliding
    output pairs). Like a `Constraint`, it *is* its violation-counting function;
    its weight is supplied separately (the systemic twin of an HG weight). -/
abbrev SystemicConstraint (n : Nat) (O : Type*) := (Fin n → O) → ℕ

/-- \*HOMOPHONY: penalizes output tuples where distinct inputs receive the same
    output, counting the colliding pairs `|{(i, j) : i < j ∧ f i = f j}|`. -/
def homophonyAvoidance {n : Nat} {O : Type*} [DecidableEq O] :
    SystemicConstraint n O :=
  fun f =>
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 = f p.2).card

-- ============================================================================
-- § 3: Joint Distribution with Systemic Constraints
-- ============================================================================

/-- **Systemic harmony** of an output tuple: `-∑ⱼ swⱼ · sconⱼ(f)`, the negated
    weighted sum of the systemic constraints' tuple-violation counts. The
    systemic twin of `harmonyScore` — same negated-weighted-sum shape, but
    scoring whole tuples; it is the coupling component of the joint score. -/
def systemicScore {n k : Nat} {O : Type*}
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O) (f : Fin n → O) : ℝ :=
  -∑ j, sw j * (scon j f : ℝ)

/-- Joint harmony score over the product space, combining classical per-mapping
    scores with the systemic tuple-level score:
    `H_joint(f) = ∑ᵢ H(iᵢ, f i) + systemicScore sw scon f`. -/
noncomputable def jointHarmonyScore {n m k : Nat} {I O : Type*}
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O)
    (f : Fin n → O) : ℝ :=
  (List.finRange n).foldl
    (λ acc i => acc + harmonyScore classicalCon classicalW (inputs i, f i)) 0
  + systemicScore sw scon f

/-- MaxEnt grammar with systemic constraints as a `CoupledSoftmax`:
    `componentScore i v = harmonyScore classicalCon classicalW (inputs i, v)` and
    `couplingScore f = systemicScore sw scon f`. The joint probability is a
    softmax over all `Fin n → O` output tuples; its marginal at position `i`
    recovers the individual mapping probability under systemic pressure. -/
noncomputable def maxEntCoupled {n m k : Nat} {I O : Type*} [Fintype O] [DecidableEq O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O) :
    Core.CoupledSoftmax (Fin n) O :=
  Core.coupledSoftmaxOfMaxEnt inputs
    (fun p => harmonyScore classicalCon classicalW p)
    (fun f => systemicScore sw scon f)

/-- Marginal probability `P(oᵢ ∣ iᵢ) = ∑_{f : f i = oᵢ} P_joint(f)`: marginalize
    the joint distribution to recover a specific mapping's probability under
    systemic pressure ([storme-2026]'s key equation). Defined through
    `CoupledSoftmax.marginal` so that factorization follows from
    `marginal_eq_independent_when_uncoupled`. -/
noncomputable def marginalProb {n m k : Nat} {I O : Type*} [Fintype O] [DecidableEq O]
    [Nonempty O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O)
    (i : Fin n) (o : O) : ℝ :=
  (maxEntCoupled inputs classicalCon classicalW sw scon).marginal i o

-- ============================================================================
-- § 4: Factorization Theorem
-- ============================================================================

/-- When all systemic weights are zero, the systemic score vanishes on every
    output tuple. -/
private lemma systemicScore_zero {n k : Nat} {O : Type*}
    {sw : Fin k → ℝ} (h_zero : ∀ j, sw j = 0)
    (scon : Fin k → SystemicConstraint n O) (f : Fin n → O) :
    systemicScore sw scon f = 0 := by
  simp only [systemicScore, h_zero, zero_mul, Finset.sum_const_zero, neg_zero]

/-- **Factorization**: when systemic weights are all zero, the marginal equals
    the classical MaxEnt probability. The coupling score is then constant (= 0),
    so `marginal_eq_independent_when_uncoupled` applies: the joint factorizes and
    each marginal equals its independent per-item softmax. -/
theorem marginal_eq_classical_when_no_systemic {n m k : Nat} {I O : Type*}
    [Fintype O] [DecidableEq O] [Nonempty O]
    (inputs : Fin n → I)
    (classicalCon : CON (I × O) m) (classicalW : Fin m → ℝ)
    (sw : Fin k → ℝ) (scon : Fin k → SystemicConstraint n O)
    (h_zero : ∀ j, sw j = 0)
    (i : Fin n) (o : O) :
    marginalProb inputs classicalCon classicalW sw scon i o =
    softmax (λ o' => harmonyScore classicalCon classicalW (inputs i, o')) o :=
  (maxEntCoupled inputs classicalCon classicalW sw scon).marginal_eq_independent_when_uncoupled
    ⟨0, systemicScore_zero h_zero scon⟩ i o

end HarmonicGrammar
