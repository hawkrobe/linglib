import Linglib.Core.Logic.OT
import Linglib.Core.Agent.RationalAction

/-!
# MaxEnt Harmonic Grammar @cite{storme-2026}

MaxEnt grammars assign probabilities to input→output mappings using the
softmax function over weighted constraint violations — the probabilistic
generalization of OT (where α → ∞ recovers categorical optimization;
see `softmax_argmax_limit`).

This module extends the basic MaxEnt setup with **systemic constraints**
(@cite{storme-2026}): constraints that evaluate *tuples* of mappings jointly
(e.g., \*HOMOPHONY penalizes distinct inputs that map to the same output).
Systemic constraints require evaluating a joint distribution over the product
space of all input→output mappings, then marginalizing to recover individual
mapping probabilities.

## Architecture

- `WeightedConstraint` extends `NamedConstraint` with a `weight : ℚ` field
- `harmonyScore` computes `-Σ wⱼ · Cⱼ(c)` in ℚ (computable)
- `MaxEntGrammar` packages inputs, candidate generation, and weighted constraints
- `SystemicConstraint` evaluates *tuples* of outputs (different type signature)
- `jointHarmonyScore` combines classical + systemic scores over the product space
- `marginalProb` marginalizes the joint to recover individual mapping probabilities

## Key theorem

`marginal_eq_classical_when_no_systemic`: when systemic constraint weight = 0,
the marginalized probability equals classical MaxEnt. This is because the joint
score decomposes additively ⇒ the joint distribution factorizes ⇒ each marginal
equals its factor.
-/

namespace Theories.Phonology.HarmonicGrammar

open Core.OT Core

-- ============================================================================
-- § 1: Weighted Constraints
-- ============================================================================

/-- A weighted constraint for MaxEnt/Harmonic Grammar.
    Extends `NamedConstraint` with a rational-valued weight. -/
structure WeightedConstraint (C : Type) extends NamedConstraint C where
  /-- Constraint weight (higher = more important). -/
  weight : ℚ

/-- Harmony score: H(c) = -Σⱼ wⱼ · Cⱼ(c).
    Negative because violations are penalized. -/
def harmonyScore {C : Type} (constraints : List (WeightedConstraint C)) (c : C) : ℚ :=
  constraints.foldl (λ acc con => acc - con.weight * (con.eval c : ℚ)) 0

/-- Harmony score as a real number, for interfacing with `softmax`. -/
noncomputable def harmonyScoreR {C : Type}
    (constraints : List (WeightedConstraint C)) (c : C) : ℝ :=
  (harmonyScore constraints c : ℝ)

-- ============================================================================
-- § 2: MaxEnt Grammar (Classical — Individual Mappings)
-- ============================================================================

/-- A MaxEnt grammar: inputs, candidate generation, and weighted constraints.
    Probability of mapping input `i` to output `o` is proportional to
    `exp(harmonyScore(i, o))`. -/
structure MaxEntGrammar (Input Output : Type) where
  /-- The set of inputs (underlying forms). -/
  inputs : List Input
  /-- Candidate generator: produces output candidates for each input. -/
  gen : Input → List Output
  /-- Weighted constraints evaluating input–output pairs. -/
  constraints : List (WeightedConstraint (Input × Output))

/-- Classical MaxEnt probability: P(o | i) = softmax over gen(i).

    This is the standard MaxEnt phonology probability, without systemic
    constraints. Uses `softmax` from `RationalAction` with α = 1. -/
noncomputable def MaxEntGrammar.prob {I O : Type} [Fintype O]
    (g : MaxEntGrammar I O) (i : I) (o : O) : ℝ :=
  softmax (λ o' => harmonyScoreR g.constraints (i, o')) 1 o

-- ============================================================================
-- § 3: Systemic Constraints
-- ============================================================================

/-- A systemic constraint evaluates a *tuple* of outputs — one per input —
    rather than individual input→output pairs.

    Example: \*HOMOPHONY counts pairs of distinct inputs that map to the same
    output. This cannot be decomposed into per-mapping evaluations.

    `n` is the number of inputs; the tuple `Fin n → O` assigns an output
    to each input index. -/
structure SystemicConstraint (n : Nat) (O : Type) where
  /-- Constraint name. -/
  name : String
  /-- Constraint weight. -/
  weight : ℚ
  /-- Evaluation function: how many violations does this output tuple incur? -/
  eval : (Fin n → O) → Nat

/-- \*HOMOPHONY: penalizes output tuples where distinct inputs receive the
    same output. Counts the number of colliding pairs.

    For n inputs, evaluates `|{(i,j) : i < j ∧ f(i) = f(j)}|`. -/
def homophonyAvoidance {n : Nat} {O : Type} [DecidableEq O]
    (w : ℚ) : SystemicConstraint n O where
  name := "*HOMOPHONY"
  weight := w
  eval := λ f =>
    let pairs := do
      let i ← (List.finRange n)
      let j ← (List.finRange n)
      if i < j && f i == f j then [1] else []
    pairs.length

-- ============================================================================
-- § 4: Joint Distribution with Systemic Constraints
-- ============================================================================

/-- Joint harmony score over the product space.
    Combines classical per-mapping scores with systemic tuple-level scores.

    H_joint(f) = Σᵢ H_classical(iᵢ, f(i)) + Σₖ (-wₖ · Sₖ(f))

    where `f : Fin n → O` is the full output tuple. -/
def jointHarmonyScore {n : Nat} {I O : Type}
    (inputs : Fin n → I)
    (classicalConstraints : List (WeightedConstraint (I × O)))
    (systemicConstraints : List (SystemicConstraint n O))
    (f : Fin n → O) : ℚ :=
  -- Sum of classical per-mapping scores
  let classical := (List.finRange n).foldl
    (λ acc i => acc + harmonyScore classicalConstraints (inputs i, f i)) 0
  -- Sum of systemic constraint penalties
  let systemic := systemicConstraints.foldl
    (λ acc sc => acc - sc.weight * (sc.eval f : ℚ)) 0
  classical + systemic

/-- Joint harmony score as ℝ. -/
noncomputable def jointHarmonyScoreR {n : Nat} {I O : Type}
    (inputs : Fin n → I)
    (classicalConstraints : List (WeightedConstraint (I × O)))
    (systemicConstraints : List (SystemicConstraint n O))
    (f : Fin n → O) : ℝ :=
  (jointHarmonyScore inputs classicalConstraints systemicConstraints f : ℝ)

/-- Joint probability over the product space `Fin n → O`:
    P_joint(f) = exp(H_joint(f)) / Σ_{f'} exp(H_joint(f')).

    This is softmax with α = 1 over all possible output tuples. -/
noncomputable def jointProb {n : Nat} {I O : Type} [Fintype O]
    (inputs : Fin n → I)
    (classicalConstraints : List (WeightedConstraint (I × O)))
    (systemicConstraints : List (SystemicConstraint n O))
    (f : Fin n → O) : ℝ :=
  softmax (jointHarmonyScoreR inputs classicalConstraints systemicConstraints) 1 f

/-- Marginal probability: marginalize the joint distribution to get
    the probability of a specific input→output mapping.

    P_marginal(oᵢ | iᵢ) = Σ_{f : f(i) = oᵢ} P_joint(f)

    This is Storme's key equation: the marginal recovers individual mapping
    probabilities that reflect systemic pressure. -/
noncomputable def marginalProb {n : Nat} {I O : Type} [Fintype O] [DecidableEq O]
    (inputs : Fin n → I)
    (classicalConstraints : List (WeightedConstraint (I × O)))
    (systemicConstraints : List (SystemicConstraint n O))
    (i : Fin n) (o : O) : ℝ :=
  ∑ f : Fin n → O,
    if f i = o then
      jointProb inputs classicalConstraints systemicConstraints f
    else 0

-- ============================================================================
-- § 5: Factorization Theorem
-- ============================================================================

/-- When systemic constraint weights are all zero, the joint distribution
    factorizes into independent per-mapping distributions, so the marginal
    equals the classical MaxEnt probability.

    Proof sketch: With zero systemic weights, `jointHarmonyScore f =
    Σᵢ harmonyScore(iᵢ, f(i))`. Since `exp(Σ) = Π exp(·)`, the joint
    distribution factorizes: `P_joint(f) = Π P_classical(f(i) | iᵢ)`.
    Marginalizing over all positions except `i` recovers
    `P_classical(o | iᵢ) · Π_{j≠i} Σ_{o'} P_classical(o' | iⱼ)`, and
    each factor `Σ_{o'} P_classical(o' | iⱼ) = 1`, leaving the classical
    probability.

    TODO: formalize the factorization argument. The key step is showing
    `exp(a + b) = exp(a) · exp(b)` lifts to `softmax` over product types
    when the score decomposes additively. -/
theorem marginal_eq_classical_when_no_systemic {n : Nat} {I O : Type}
    [Fintype O] [DecidableEq O] [Nonempty O]
    (inputs : Fin n → I)
    (classicalConstraints : List (WeightedConstraint (I × O)))
    (systemicConstraints : List (SystemicConstraint n O))
    (h_zero : ∀ sc ∈ systemicConstraints, sc.weight = 0)
    (i : Fin n) (o : O) :
    marginalProb inputs classicalConstraints systemicConstraints i o =
    softmax (λ o' => harmonyScoreR classicalConstraints (inputs i, o')) 1 o := by
  sorry

end Theories.Phonology.HarmonicGrammar
