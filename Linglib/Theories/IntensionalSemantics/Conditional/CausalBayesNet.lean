/-
# Causal Bayes Net Infrastructure

Infrastructure for modeling causal dependencies between variables.

This module provides types for:
- Causal relations between two variables (A→C, C→A, A⊥C)
- Noisy-OR parameterization for probabilistic dependencies
- World states as distributions over atomic propositions

## Insight

Following Grusdt, Lassiter & Franke (2022), conditionals are used to communicate
about causal/correlational relationships in the world. The listener must infer:
1. The probability distribution (WorldState)
2. The underlying causal structure (CausalRelation)

## References

- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
- Pearl (2009). Causality.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace IntensionalSemantics.Conditional.CausalBayesNet

-- Causal Relations

/--
Causal relations between two binary variables A (antecedent) and C (consequent).

These represent the possible causal structures:
- `ACausesC`: A causally influences C (A → C)
- `CCausesA`: C causally influences A (C → A)
- `Independent`: No causal link between A and C (A ⊥ C)

The paper focuses on these three structures because they are distinguishable
through conditional assertion patterns.
-/
inductive CausalRelation
  | ACausesC    -- A → C: antecedent causes consequent
  | CCausesA    -- C → A: consequent causes antecedent
  | Independent -- A ⊥ C: no causal link
  deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString CausalRelation where
  toString
    | .ACausesC => "A→C"
    | .CCausesA => "C→A"
    | .Independent => "A⊥C"

-- Noisy-OR Parameterization

/--
Noisy-OR parameterization for a causal link (simplified, no proof fields).

In a Noisy-OR model:
- `background` (b): P(C | ¬A) - the background rate without the cause
- `power` (Δ): The causal power = P(C | A) - P(C | ¬A)

The probability of the effect given the cause is:
  P(C | A) = background + power

Constraints (expected but not enforced at type level):
- 0 ≤ background ≤ 1
- 0 ≤ background + power ≤ 1

Reference: Cheng (1997), From covariation to causation.
-/
structure NoisyOR where
  /-- Background rate: P(C | ¬A) -/
  background : ℚ
  /-- Causal power: P(C | A) - P(C | ¬A) -/
  power : ℚ
  deriving Repr, DecidableEq, BEq

namespace NoisyOR

/-- P(C | A) in the Noisy-OR model -/
def pCGivenA (n : NoisyOR) : ℚ := n.background + n.power

/-- P(C | ¬A) in the Noisy-OR model -/
def pCGivenNotA (n : NoisyOR) : ℚ := n.background

/-- Check if parameters are valid -/
def isValid (n : NoisyOR) : Bool :=
  0 ≤ n.background && n.background ≤ 1 &&
  0 ≤ n.background + n.power && n.background + n.power ≤ 1

/-- Deterministic cause: P(C|A) = 1, P(C|¬A) = 0 -/
def deterministic : NoisyOR := { background := 0, power := 1 }

/-- No effect: P(C|A) = P(C|¬A) = 0 -/
def noEffect : NoisyOR := { background := 0, power := 0 }

/-- Always-on: P(C|A) = P(C|¬A) = 1 -/
def alwaysOn : NoisyOR := { background := 1, power := 0 }

/-- Half-half: P(C|A) = 0.5, P(C|¬A) = 0 -/
def half : NoisyOR := { background := 0, power := 1/2 }

end NoisyOR

-- World States as Probability Distributions

/--
A world state representing a probability distribution over two binary variables.

Unlike typical RSA models where worlds are atomic states, in the conditional
semantics of Grusdt et al. (2022), a "world" is itself a probability distribution.
This is because conditionals make claims about probabilities (P(C|A) > θ).

The four atomic states are:
- w₀: ¬A ∧ ¬C (neither A nor C)
- wA: A ∧ ¬C (A but not C)
- wC: ¬A ∧ C (C but not A)
- wAC: A ∧ C (both A and C)

We store the marginals and joint for efficiency:
- pA: P(A)
- pC: P(C)
- pAC: P(A ∧ C)

The other probabilities are derived:
- P(¬A) = 1 - pA
- P(¬C) = 1 - pC
- P(A ∧ ¬C) = pA - pAC
- P(¬A ∧ C) = pC - pAC
- P(¬A ∧ ¬C) = 1 - pA - pC + pAC
-/
structure WorldState where
  /-- Marginal probability P(A) -/
  pA : ℚ
  /-- Marginal probability P(C) -/
  pC : ℚ
  /-- Joint probability P(A ∧ C) -/
  pAC : ℚ
  deriving Repr, DecidableEq, BEq

namespace WorldState

-- Validity Check

/-- Check if a WorldState represents a valid probability distribution -/
def isValid (w : WorldState) : Bool :=
  0 ≤ w.pA && w.pA ≤ 1 &&
  0 ≤ w.pC && w.pC ≤ 1 &&
  0 ≤ w.pAC && w.pAC ≤ min w.pA w.pC &&
  w.pA + w.pC - w.pAC ≤ 1

-- Derived Probabilities

/-- P(A ∧ ¬C) = P(A) - P(A ∧ C) -/
def pANotC (w : WorldState) : ℚ := w.pA - w.pAC

/-- P(¬A ∧ C) = P(C) - P(A ∧ C) -/
def pNotAC (w : WorldState) : ℚ := w.pC - w.pAC

/-- P(¬A ∧ ¬C) = 1 - P(A) - P(C) + P(A ∧ C) -/
def pNotANotC (w : WorldState) : ℚ := 1 - w.pA - w.pC + w.pAC

/-- P(¬A) = 1 - P(A) -/
def pNotA (w : WorldState) : ℚ := 1 - w.pA

/-- P(¬C) = 1 - P(C) -/
def pNotC (w : WorldState) : ℚ := 1 - w.pC

-- Conditional Probabilities

/-- P(C | A) = P(A ∧ C) / P(A), or 0 if P(A) = 0 -/
def pCGivenA (w : WorldState) : ℚ :=
  if w.pA > 0 then w.pAC / w.pA else 0

/-- P(C | ¬A) = P(¬A ∧ C) / P(¬A), or 0 if P(¬A) = 0 -/
def pCGivenNotA (w : WorldState) : ℚ :=
  let pNotA := 1 - w.pA
  if pNotA > 0 then w.pNotAC / pNotA else 0

/-- P(A | C) = P(A ∧ C) / P(C), or 0 if P(C) = 0 -/
def pAGivenC (w : WorldState) : ℚ :=
  if w.pC > 0 then w.pAC / w.pC else 0

/-- P(A | ¬C) = P(A ∧ ¬C) / P(¬C), or 0 if P(¬C) = 0 -/
def pAGivenNotC (w : WorldState) : ℚ :=
  let pNotC := 1 - w.pC
  if pNotC > 0 then w.pANotC / pNotC else 0

-- Independence and Correlation

/-- Check if A and C are probabilistically independent: P(A ∧ C) = P(A) · P(C) -/
def isIndependent (w : WorldState) : Bool :=
  w.pAC == w.pA * w.pC

/-- Check if A and C are positively correlated: P(A ∧ C) > P(A) · P(C) -/
def isPositivelyCorrelated (w : WorldState) : Bool :=
  w.pAC > w.pA * w.pC

/-- Check if A and C are negatively correlated: P(A ∧ C) < P(A) · P(C) -/
def isNegativelyCorrelated (w : WorldState) : Bool :=
  w.pAC < w.pA * w.pC

-- Constructors

/-- Create a WorldState from marginals assuming independence -/
def independent (pA pC : ℚ) : WorldState :=
  { pA := pA, pC := pC, pAC := pA * pC }

/-- Create a WorldState with perfect correlation (A ↔ C) -/
def perfectCorrelation (p : ℚ) : WorldState :=
  { pA := p, pC := p, pAC := p }

/-- Create a WorldState with no correlation (A ∧ C never happens) -/
def mutuallyExclusive (pA pC : ℚ) : WorldState :=
  { pA := pA, pC := pC, pAC := 0 }

-- Example World States

/-- Deterministic: A always causes C, P(A) = P(C) = P(A∧C) = 1/2 -/
def deterministicACausesC : WorldState :=
  { pA := 1/2, pC := 1/2, pAC := 1/2 }

/-- No correlation: A and C are independent with P = 1/2 each -/
def independentExample : WorldState :=
  { pA := 1/2, pC := 1/2, pAC := 1/4 }

/-- High conditional probability: P(C|A) = 0.9 -/
def highConditional : WorldState :=
  { pA := 1/2, pC := 1/2, pAC := 9/20 }  -- P(C|A) = (9/20)/(1/2) = 0.9

/-- Low conditional probability: P(C|A) = 0.2 -/
def lowConditional : WorldState :=
  { pA := 1/2, pC := 1/2, pAC := 1/10 }  -- P(C|A) = (1/10)/(1/2) = 0.2

-- Validity Theorems

/--
A propositional version of isValid for theorem proving.
-/
def IsValid (w : WorldState) : Prop :=
  0 ≤ w.pA ∧ w.pA ≤ 1 ∧
  0 ≤ w.pC ∧ w.pC ≤ 1 ∧
  0 ≤ w.pAC ∧ w.pAC ≤ min w.pA w.pC ∧
  w.pA + w.pC - w.pAC ≤ 1

/--
Validity implies P(A) is in [0,1].
-/
theorem valid_implies_pA_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pA ∧ w.pA ≤ 1 := ⟨h.1, h.2.1⟩

/--
Validity implies P(C) is in [0,1].
-/
theorem valid_implies_pC_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pC ∧ w.pC ≤ 1 := ⟨h.2.2.1, h.2.2.2.1⟩

/--
Validity implies P(A ∧ C) is in [0, min(P(A), P(C))].
-/
theorem valid_implies_pAC_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pAC ∧ w.pAC ≤ min w.pA w.pC := ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/--
**Validity implies P(C|A) is bounded** (when P(A) > 0).

If the world state is valid and P(A) > 0, then 0 ≤ P(C|A) ≤ 1.
-/
theorem valid_implies_pCGivenA_bounded (w : WorldState) (h : w.IsValid) (hA : 0 < w.pA) :
    0 ≤ w.pCGivenA ∧ w.pCGivenA ≤ 1 := by
  simp only [pCGivenA, gt_iff_lt, hA, ↓reduceIte]
  constructor
  · apply div_nonneg h.2.2.2.2.1 (le_of_lt hA)
  · have hAC_le : w.pAC ≤ w.pA := le_trans h.2.2.2.2.2.1 (min_le_left w.pA w.pC)
    have hA_ne : w.pA ≠ 0 := ne_of_gt hA
    calc w.pAC / w.pA ≤ w.pA / w.pA := by
             apply div_le_div_of_nonneg_right hAC_le (le_of_lt hA)
         _ = 1 := div_self hA_ne

/--
**Validity implies P(C|¬A) is bounded** (when P(A) < 1).

If the world state is valid and P(A) < 1, then 0 ≤ P(C|¬A) ≤ 1.
-/
theorem valid_implies_pCGivenNotA_bounded (w : WorldState) (h : w.IsValid) (hA : w.pA < 1) :
    0 ≤ w.pCGivenNotA ∧ w.pCGivenNotA ≤ 1 := by
  simp only [pCGivenNotA, pNotAC]
  have hNotA_pos : 0 < 1 - w.pA := by linarith
  simp only [gt_iff_lt, hNotA_pos, ↓reduceIte]
  constructor
  · apply div_nonneg
    · -- P(¬A ∧ C) = P(C) - P(A ∧ C) ≥ 0
      have : w.pAC ≤ w.pC := le_trans h.2.2.2.2.2.1 (min_le_right w.pA w.pC)
      linarith
    · exact le_of_lt hNotA_pos
  · -- P(C|¬A) = P(¬A ∧ C) / P(¬A) ≤ 1, i.e., P(¬A ∧ C) ≤ P(¬A)
    have hNotAC_le : w.pC - w.pAC ≤ 1 - w.pA := by linarith [h.2.2.2.2.2.2]
    have hNotA_ne : 1 - w.pA ≠ 0 := ne_of_gt hNotA_pos
    calc (w.pC - w.pAC) / (1 - w.pA) ≤ (1 - w.pA) / (1 - w.pA) := by
             apply div_le_div_of_nonneg_right hNotAC_le (le_of_lt hNotA_pos)
         _ = 1 := div_self hNotA_ne

/--
**Law of Total Probability**.

For a valid world state: P(C) = P(C|A) · P(A) + P(C|¬A) · P(¬A)

This requires P(A) ∈ (0, 1) for both conditional probabilities to be defined.
-/
theorem law_of_total_probability (w : WorldState) (_h : w.IsValid)
    (hA_pos : 0 < w.pA) (hA_lt_one : w.pA < 1) :
    w.pC = w.pCGivenA * w.pA + w.pCGivenNotA * (1 - w.pA) := by
  simp only [pCGivenA, pCGivenNotA, pNotAC]
  have hNotA_pos : 0 < 1 - w.pA := by linarith
  simp only [gt_iff_lt, hA_pos, hNotA_pos, ↓reduceIte]
  have hA_ne : w.pA ≠ 0 := ne_of_gt hA_pos
  have hNotA_ne : 1 - w.pA ≠ 0 := ne_of_gt hNotA_pos
  field_simp
  ring

/--
**Bayes' Theorem**.

P(A|C) = P(C|A) · P(A) / P(C)

This requires P(A) > 0 and P(C) > 0.
-/
theorem bayes_theorem (w : WorldState) (hA : 0 < w.pA) (hC : 0 < w.pC) :
    w.pAGivenC = w.pCGivenA * w.pA / w.pC := by
  simp only [pAGivenC, pCGivenA]
  simp only [gt_iff_lt, hA, hC, ↓reduceIte]
  have hA_ne : w.pA ≠ 0 := ne_of_gt hA
  -- P(A|C) = P(AC)/P(C) = (P(AC)/P(A)) * P(A) / P(C)
  rw [div_mul_eq_mul_div]
  congr 1
  rw [mul_div_assoc, div_self hA_ne, mul_one]

end WorldState

-- Fintype for Discrete World States

/--
For computational purposes, we often work with a finite set of discretized
world states. This structure packages a list of world states for enumeration.
-/
structure DiscreteWorldSpace where
  /-- The finite set of world states -/
  states : List WorldState
  /-- States are non-empty -/
  nonempty : states ≠ []

end IntensionalSemantics.Conditional.CausalBayesNet
