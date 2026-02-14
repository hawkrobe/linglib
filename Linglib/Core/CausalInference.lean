import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Rat
import Linglib.Core.CausalModel

/-!
# Causal Inference Infrastructure

Unified module for causal and counterfactual reasoning, combining:

1. **Counterfactual probability spaces** (Park, Yang & Icard 2026): joint
   distributions on ΩF × ΩCF, causal kernels, backtracking vs interventional queries
2. **Causal Bayes nets** (Grusdt, Lassiter & Franke 2022): `CausalRelation`,
   `NoisyOR` parameterization, `WorldState` as probability distributions over
   two binary variables
3. **Bridges**: `WorldState ↔ CFProbSpace Bool Bool`, `CausalDynamics → FinCausalKernel`

## Key Concepts

- **CFProbSpace**: Joint distribution on ΩF × ΩCF encoding shared factual–
  counterfactual information
- **FinCausalKernel**: Transition kernel K(ωF, ωCF) for interventional queries
- **CFCausalSpace**: CFProbSpace + causal kernel satisfying no-cross-world-effect
- **WorldState**: Distribution over two binary variables (P(A), P(C), P(A∧C))
- **CausalRelation**: A→C, C→A, or A⊥C causal structure
- **NoisyOR**: Noisy-OR parameterization for probabilistic causal links

## References

- Park, Y., Yang, S. & Icard, T. (2026). Counterfactual probability spaces.
- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
- Pearl (2009). Causality.
-/

namespace Core.CausalInference

-- Counterfactual Probability Spaces

/--
**Counterfactual probability space** (Park, Yang & Icard 2026).

A joint distribution on ΩF × ΩCF where:
- ΩF indexes factual worlds
- ΩCF indexes counterfactual worlds
- `prob` encodes shared information between factual and counterfactual

The amount of correlation between the two components determines the
"shared information" — from fully independent (no backtracking) to
fully synchronized (factual determines counterfactual).
-/
structure CFProbSpace (ΩF ΩCF : Type) [Fintype ΩF] [Fintype ΩCF] where
  /-- Joint distribution P(ωF, ωCF) -/
  prob : ΩF × ΩCF → ℚ
  /-- All probabilities are nonnegative -/
  nonneg : ∀ ω, 0 ≤ prob ω
  /-- Probabilities sum to 1 -/
  sum_one : ∑ ω : ΩF × ΩCF, prob ω = 1

variable {ΩF ΩCF : Type} [Fintype ΩF] [Fintype ΩCF]

-- Marginals

/-- Factual marginal: P(ωF) = ∑_{ωCF} P(ωF, ωCF) -/
def marginalF [DecidableEq ΩF] (s : CFProbSpace ΩF ΩCF) (ωF : ΩF) : ℚ :=
  ∑ ωCF : ΩCF, s.prob (ωF, ωCF)

/-- Counterfactual marginal: P(ωCF) = ∑_{ωF} P(ωF, ωCF) -/
def marginalCF [DecidableEq ΩCF] (s : CFProbSpace ΩF ΩCF) (ωCF : ΩCF) : ℚ :=
  ∑ ωF : ΩF, s.prob (ωF, ωCF)

-- Conditioning

/-- P(ωCF | ωF) = P(ωF, ωCF) / P(ωF), or 0 if P(ωF) = 0 -/
def condOnF [DecidableEq ΩF] (s : CFProbSpace ΩF ΩCF) (ωF : ΩF) (ωCF : ΩCF) : ℚ :=
  let m := marginalF s ωF
  if m > 0 then s.prob (ωF, ωCF) / m else 0

/-- P(ωF | ωCF) = P(ωF, ωCF) / P(ωCF), or 0 if P(ωCF) = 0 -/
def condOnCF [DecidableEq ΩCF] (s : CFProbSpace ΩF ΩCF) (ωF : ΩF) (ωCF : ΩCF) : ℚ :=
  let m := marginalCF s ωCF
  if m > 0 then s.prob (ωF, ωCF) / m else 0

-- Shared Information Extremes

/-- The space is **independent**: P(ωF, ωCF) = P(ωF) · P(ωCF) for all ω.
    No shared information between factual and counterfactual. -/
def isIndependent [DecidableEq ΩF] [DecidableEq ΩCF]
    (s : CFProbSpace ΩF ΩCF) : Prop :=
  ∀ ωF ωCF, s.prob (ωF, ωCF) = marginalF s ωF * marginalCF s ωCF

/-- The space is **synchronized**: support is diagonal.
    P(ωF, ωCF) > 0 implies ωF = ωCF (same-type version). -/
def isSynchronized [DecidableEq ΩF] (s : CFProbSpace ΩF ΩF) : Prop :=
  ∀ ωF ωCF, s.prob (ωF, ωCF) > 0 → ωF = ωCF

/-- The space is **symmetric**: P(a, b) = P(b, a) (same-type version). -/
def isSymmetric {Ω : Type} [Fintype Ω] (s : CFProbSpace Ω Ω) : Prop :=
  ∀ a b, s.prob (a, b) = s.prob (b, a)

-- Counterfactual Queries

/-- **Backtracking counterfactual probability** (Example 3.4).

    "Given factual event A, what's the probability of counterfactual event B?"

    P(B^CF | A^F) = ∑_{ωF ∈ A, ωCF ∈ B} P(ωF, ωCF) / ∑_{ωF ∈ A} marginalF(ωF)

    This conditions on factual observation, reading off the counterfactual
    probability via the shared information in the joint distribution. -/
def backtrackerProb [DecidableEq ΩF] [DecidableEq ΩCF]
    (s : CFProbSpace ΩF ΩCF) (A : ΩF → Bool) (B : ΩCF → Bool) : ℚ :=
  let num := ∑ ω : ΩF × ΩCF, if A ω.1 && B ω.2 then s.prob ω else 0
  let den := ∑ ω : ΩF × ΩCF, if A ω.1 then s.prob ω else 0
  if den > 0 then num / den else 0

-- Finite Causal Kernels

/--
**Finite causal kernel** (simplified version of Def 4.1).

K(ωF, ωCF) gives the probability of counterfactual outcome ωCF given
interventional context ωF. Unlike conditioning (which uses the joint),
the kernel represents an *external* causal mechanism.
-/
structure FinCausalKernel (ΩF ΩCF : Type) [Fintype ΩF] [Fintype ΩCF] where
  /-- K(ωF, ωCF) = probability of ωCF given intervention context ωF -/
  kernel : ΩF → ΩCF → ℚ
  /-- All kernel values are nonnegative -/
  nonneg : ∀ ωF ωCF, 0 ≤ kernel ωF ωCF
  /-- Each row sums to 1 -/
  sum_one : ∀ ωF, ∑ ωCF, kernel ωF ωCF = 1

/-- **Interventional counterfactual probability**.

    Uses the causal kernel rather than conditioning:
    P_do(B) = ∑_{ωF} marginalF(ωF) · K(ωF, B)

    This differs from `backtrackerProb` when K ≠ conditional. -/
def interventionalProb [DecidableEq ΩF] [DecidableEq ΩCF]
    (s : CFProbSpace ΩF ΩCF) (k : FinCausalKernel ΩF ΩCF)
    (B : ΩCF → Bool) : ℚ :=
  ∑ ωF : ΩF, marginalF s ωF *
    (∑ ωCF : ΩCF, if B ωCF then k.kernel ωF ωCF else 0)

-- Causal Counterfactual Spaces

/--
**Counterfactual causal space** (Def 4.1).

A counterfactual probability space equipped with a causal kernel satisfying
the no-cross-world-effect axiom: intervening in one world doesn't change
the marginal of the other.
-/
structure CFCausalSpace (ΩF ΩCF : Type) [Fintype ΩF] [Fintype ΩCF]
    [DecidableEq ΩF] [DecidableEq ΩCF] extends CFProbSpace ΩF ΩCF where
  /-- The causal kernel -/
  causal : FinCausalKernel ΩF ΩCF
  /-- No cross-world causal effect (Def 4.1(ii)):
      intervening in one world doesn't change marginal of the other. -/
  noCrossWorld : ∀ ωCF,
    ∑ ωF, causal.kernel ωF ωCF * marginalF toCFProbSpace ωF =
      marginalCF toCFProbSpace ωCF

-- Point-mass kernel (for deterministic models)

/-- A **point-mass kernel**: deterministic mapping f : ΩF → ΩCF. -/
def pointMassKernel [DecidableEq ΩCF] (f : ΩF → ΩCF) : FinCausalKernel ΩF ΩCF where
  kernel := λ ωF ωCF => if f ωF = ωCF then 1 else 0
  nonneg := by
    intro ωF ωCF
    split <;> norm_num
  sum_one := by
    intro ωF
    simp [Finset.sum_ite_eq']

-- Key Theorems

section Theorems

variable [DecidableEq ΩF] [DecidableEq ΩCF]

/-- Factual marginal is nonnegative. -/
theorem marginalF_nonneg (s : CFProbSpace ΩF ΩCF) (ωF : ΩF) :
    0 ≤ marginalF s ωF := by
  simp only [marginalF]
  apply Finset.sum_nonneg
  intro ωCF _
  exact s.nonneg (ωF, ωCF)

/-- Factual marginal sums to 1. -/
theorem marginalF_sum_one (s : CFProbSpace ΩF ΩCF) :
    ∑ ωF : ΩF, marginalF s ωF = 1 := by
  simp only [marginalF]
  rw [← s.sum_one, ← Finset.sum_product']
  simp [Finset.sum_congr rfl (λ x _ => rfl)]

/-- Counterfactual marginal is nonnegative. -/
theorem marginalCF_nonneg (s : CFProbSpace ΩF ΩCF) (ωCF : ΩCF) :
    0 ≤ marginalCF s ωCF := by
  simp only [marginalCF]
  apply Finset.sum_nonneg
  intro ωF _
  exact s.nonneg (ωF, ωCF)

/-- Counterfactual marginal sums to 1. -/
theorem marginalCF_sum_one (s : CFProbSpace ΩF ΩCF) :
    ∑ ωCF : ΩCF, marginalCF s ωCF = 1 := by
  simp only [marginalCF]
  rw [← s.sum_one, ← Finset.sum_product_right']
  simp [Finset.sum_congr rfl (λ x _ => rfl)]

/-- In an independent space, conditioning equals the marginal
    (no information shared). -/
theorem independent_cond_eq_marginal
    (s : CFProbSpace ΩF ΩCF) (h : isIndependent s)
    (ωF : ΩF) (ωCF : ΩCF) (hm : marginalF s ωF > 0) :
    condOnF s ωF ωCF = marginalCF s ωCF := by
  simp only [condOnF, hm, ↓reduceIte]
  rw [h ωF ωCF]
  have hm_ne : marginalF s ωF ≠ 0 := ne_of_gt hm
  rw [mul_div_cancel_left₀ _ hm_ne]

/-- In a synchronized space, conditioning is a point mass:
    P(ωCF | ωF) = 1 if ωCF = ωF, else 0 (when P(ωF) > 0). -/
theorem synchronized_cond_point_mass
    (s : CFProbSpace ΩF ΩF) (h : isSynchronized s)
    (ωF ωCF : ΩF) (hm : marginalF s ωF > 0)
    (h_neq : ωF ≠ ωCF) :
    condOnF s ωF ωCF = 0 := by
  simp only [condOnF, hm, ↓reduceIte]
  -- P(ωF, ωCF) = 0 because synchronized and ωF ≠ ωCF
  have h_zero : s.prob (ωF, ωCF) = 0 := by
    by_contra h_pos
    have : s.prob (ωF, ωCF) > 0 := by
      rcases lt_or_eq_of_le (s.nonneg (ωF, ωCF)) with h' | h'
      · exact h'
      · exact absurd h'.symm h_pos
    exact h_neq (h ωF ωCF this)
  simp [h_zero]

/-- Backtracking and interventional queries differ when K ≠ conditional.

    TODO: Full proof requires constructing a specific counterexample where
    the kernel diverges from the conditional distribution. -/
theorem backtracker_ne_interventional_possible :
    ∃ (s : CFProbSpace Bool Bool) (k : FinCausalKernel Bool Bool)
      (A : Bool → Bool) (B : Bool → Bool),
      backtrackerProb s A B ≠ interventionalProb s k B := by
  sorry

end Theorems

-- Causal Relations (absorbed from CausalBayesNet)

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

-- WorldState ↔ CFProbSpace Bool Bool

/--
Convert a valid `WorldState` to a `CFProbSpace Bool Bool`.

The four cells of the joint distribution are:
- P(true, true)  = P(A ∧ C)   = w.pAC
- P(true, false) = P(A ∧ ¬C)  = w.pA - w.pAC
- P(false, true) = P(¬A ∧ C)  = w.pC - w.pAC
- P(false, false)= P(¬A ∧ ¬C) = 1 - w.pA - w.pC + w.pAC

This reveals `WorldState` as a degenerate 2-variable counterfactual
probability space: factual A, counterfactual C.
-/
def WorldState.toCFProbSpace (w : WorldState) (h : w.IsValid) :
    CFProbSpace Bool Bool where
  prob := λ ω => match ω with
    | (true, true) => w.pAC
    | (true, false) => w.pA - w.pAC
    | (false, true) => w.pC - w.pAC
    | (false, false) => 1 - w.pA - w.pC + w.pAC
  nonneg := by
    intro ⟨a, b⟩
    rcases a with _ | _ <;> rcases b with _ | _ <;> simp only
    · -- (false, false): 1 - w.pA - w.pC + w.pAC ≥ 0
      linarith [h.2.2.2.2.2.2]
    · -- (false, true): w.pC - w.pAC ≥ 0
      linarith [h.2.2.2.2.2.1, min_le_right w.pA w.pC]
    · -- (true, false): w.pA - w.pAC ≥ 0
      linarith [h.2.2.2.2.2.1, min_le_left w.pA w.pC]
    · -- (true, true): w.pAC ≥ 0
      exact h.2.2.2.2.1
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    ring

/-- Extract a `WorldState` from any `CFProbSpace Bool Bool`. -/
def CFProbSpace.toWorldState (s : CFProbSpace Bool Bool) : WorldState where
  pA := s.prob (true, true) + s.prob (true, false)
  pC := s.prob (true, true) + s.prob (false, true)
  pAC := s.prob (true, true)

/-- `WorldState` conditioning matches `CFProbSpace` conditioning.

    P(C|A) in the WorldState equals condOnF at (true, true) in the
    corresponding CFProbSpace (when P(A) > 0). -/
theorem worldState_pCGivenA_eq_condOnF (w : WorldState) (h : w.IsValid)
    (hA : 0 < w.pA) :
    w.pCGivenA = condOnF (w.toCFProbSpace h) true true := by
  simp only [WorldState.pCGivenA, condOnF, marginalF, WorldState.toCFProbSpace,
             Fintype.sum_bool, gt_iff_lt, hA, ↓reduceIte]
  -- marginalF at true = w.pAC + (w.pA - w.pAC) = w.pA
  have h_marginal : w.pAC + (w.pA - w.pAC) = w.pA := by ring
  rw [h_marginal]
  simp only [hA, ↓reduceIte]

-- CausalDynamics → FinCausalKernel bridge

open Core.CausalModel in
/-- A deterministic causal model induces a **point-mass causal kernel**.

    K(true, ωCF) = 1 if normalDevelopment(bg + cause) has effect = ωCF, else 0
    K(false, ωCF) = 1 if normalDevelopment(bg - cause) has effect = ωCF, else 0

    This bridges `causalCounterfactual` (which uses `normalDevelopment` +
    `interventionSelection`) to the kernel framework. -/
def dynamicsToKernel (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : FinCausalKernel Bool Bool :=
  pointMassKernel (λ causeVal =>
    let s := bg.extend cause causeVal
    (normalDevelopment dyn s).hasValue effect true)

/-- **Backtracking counterfactual**: condition on factual observation,
    read off counterfactual probability.

    Given a `CFProbSpace Bool Bool`, conditions on the factual component
    (A observed) and reads off the counterfactual (C). -/
def backtrackerCounterfactual (space : CFProbSpace Bool Bool)
    (factualObs : Bool) (cfQuery : Bool) : ℚ :=
  condOnF space factualObs cfQuery

end Core.CausalInference
