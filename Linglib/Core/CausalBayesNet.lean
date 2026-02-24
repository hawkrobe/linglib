import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Field.Rat

/-!
# Causal Bayes Net

Two-node causal Bayesian network infrastructure: directed causal structure
over two binary variables, noisy-OR parameterization, and probability
distributions with conditional probability, independence, and correlation.

- **CausalRelation**: A→C, C→A, or A⊥C causal structure
- **NoisyOR**: Noisy-OR parameterization for probabilistic causal links (Cheng 1997)
- **WorldState**: Joint distribution over two binary variables A and C

## References

- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
- Cheng, P. (1997). From covariation to causation.
- Pearl, J. (2000/2009). *Causality: Models, Reasoning, and Inference*.
-/

namespace Core.CausalBayesNet

-- Causal Relations

/-- Causal relations between two binary variables A and C.
    Used by Grusdt, Lassiter & Franke (2022) for conditional semantics. -/
inductive CausalRelation
  | ACausesC    -- A → C
  | CCausesA    -- C → A
  | Independent -- A ⊥ C
  deriving Repr, DecidableEq, BEq, Inhabited

instance : ToString CausalRelation where
  toString
    | .ACausesC => "A→C"
    | .CCausesA => "C→A"
    | .Independent => "A⊥C"

-- Noisy-OR Parameterization

/-- Noisy-OR parameterization for a causal link (Cheng 1997).

    - `background` (b): P(C | ¬A) — background rate
    - `power` (Δ): P(C | A) - P(C | ¬A) — causal power -/
structure NoisyOR where
  /-- Background rate: P(C | ¬A) -/
  background : ℚ
  /-- Causal power: P(C | A) - P(C | ¬A) -/
  power : ℚ
  deriving Repr, DecidableEq, BEq

namespace NoisyOR

/-- P(C | A) in the Noisy-OR model. -/
def pCGivenA (n : NoisyOR) : ℚ := n.background + n.power

/-- P(C | ¬A) in the Noisy-OR model. -/
def pCGivenNotA (n : NoisyOR) : ℚ := n.background

/-- Check if parameters are valid. -/
def isValid (n : NoisyOR) : Bool :=
  0 ≤ n.background && n.background ≤ 1 &&
  0 ≤ n.background + n.power && n.background + n.power ≤ 1

/-- Deterministic cause: P(C|A) = 1, P(C|¬A) = 0. -/
def deterministic : NoisyOR := { background := 0, power := 1 }

/-- No effect: P(C|A) = P(C|¬A) = 0. -/
def noEffect : NoisyOR := { background := 0, power := 0 }

/-- Always-on: P(C|A) = P(C|¬A) = 1. -/
def alwaysOn : NoisyOR := { background := 1, power := 0 }

end NoisyOR

-- World States as Probability Distributions

/-- A probability distribution over two binary variables A and C.

    Used by Grusdt et al. (2022): a "world" is a probability distribution
    because conditionals make claims about probabilities (P(C|A) > θ). -/
structure WorldState where
  /-- Marginal probability P(A) -/
  pA : ℚ
  /-- Marginal probability P(C) -/
  pC : ℚ
  /-- Joint probability P(A ∧ C) -/
  pAC : ℚ
  deriving Repr, DecidableEq, BEq

namespace WorldState

-- Validity

/-- Check if a WorldState represents a valid probability distribution. -/
def isValid (w : WorldState) : Bool :=
  0 ≤ w.pA && w.pA ≤ 1 &&
  0 ≤ w.pC && w.pC ≤ 1 &&
  0 ≤ w.pAC && w.pAC ≤ min w.pA w.pC &&
  w.pA + w.pC - w.pAC ≤ 1

-- Derived Probabilities

/-- P(A ∧ ¬C) -/
def pANotC (w : WorldState) : ℚ := w.pA - w.pAC

/-- P(¬A ∧ C) -/
def pNotAC (w : WorldState) : ℚ := w.pC - w.pAC

/-- P(¬A ∧ ¬C) -/
def pNotANotC (w : WorldState) : ℚ := 1 - w.pA - w.pC + w.pAC

/-- P(¬A) -/
def pNotA (w : WorldState) : ℚ := 1 - w.pA

/-- P(¬C) -/
def pNotC (w : WorldState) : ℚ := 1 - w.pC

-- Conditional Probabilities

/-- P(C | A), or 0 if P(A) = 0. -/
def pCGivenA (w : WorldState) : ℚ :=
  if w.pA > 0 then w.pAC / w.pA else 0

/-- P(C | ¬A), or 0 if P(¬A) = 0. -/
def pCGivenNotA (w : WorldState) : ℚ :=
  let pNotA := 1 - w.pA
  if pNotA > 0 then w.pNotAC / pNotA else 0

/-- P(A | C), or 0 if P(C) = 0. -/
def pAGivenC (w : WorldState) : ℚ :=
  if w.pC > 0 then w.pAC / w.pC else 0

/-- P(A | ¬C), or 0 if P(¬C) = 0. -/
def pAGivenNotC (w : WorldState) : ℚ :=
  let pNotC := 1 - w.pC
  if pNotC > 0 then w.pANotC / pNotC else 0

-- Independence and Correlation

/-- P(A ∧ C) = P(A) · P(C). -/
def isIndependent (w : WorldState) : Bool :=
  w.pAC == w.pA * w.pC

/-- P(A ∧ C) > P(A) · P(C). -/
def isPositivelyCorrelated (w : WorldState) : Bool :=
  w.pAC > w.pA * w.pC

/-- P(A ∧ C) < P(A) · P(C). -/
def isNegativelyCorrelated (w : WorldState) : Bool :=
  w.pAC < w.pA * w.pC

-- Constructors

/-- WorldState from marginals assuming independence. -/
def independent (pA pC : ℚ) : WorldState :=
  { pA := pA, pC := pC, pAC := pA * pC }

/-- WorldState with perfect correlation (A ↔ C). -/
def perfectCorrelation (p : ℚ) : WorldState :=
  { pA := p, pC := p, pAC := p }

/-- WorldState where A ∧ C never happens. -/
def mutuallyExclusive (pA pC : ℚ) : WorldState :=
  { pA := pA, pC := pC, pAC := 0 }

-- Validity Theorems

/-- Propositional version of isValid for theorem proving. -/
def IsValid (w : WorldState) : Prop :=
  0 ≤ w.pA ∧ w.pA ≤ 1 ∧
  0 ≤ w.pC ∧ w.pC ≤ 1 ∧
  0 ≤ w.pAC ∧ w.pAC ≤ min w.pA w.pC ∧
  w.pA + w.pC - w.pAC ≤ 1

theorem valid_implies_pA_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pA ∧ w.pA ≤ 1 := ⟨h.1, h.2.1⟩

theorem valid_implies_pC_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pC ∧ w.pC ≤ 1 := ⟨h.2.2.1, h.2.2.2.1⟩

theorem valid_implies_pAC_bounded (w : WorldState) (h : w.IsValid) :
    0 ≤ w.pAC ∧ w.pAC ≤ min w.pA w.pC := ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Validity implies 0 ≤ P(C|A) ≤ 1. -/
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

/-- Validity implies 0 ≤ P(C|¬A) ≤ 1. -/
theorem valid_implies_pCGivenNotA_bounded (w : WorldState) (h : w.IsValid) (hA : w.pA < 1) :
    0 ≤ w.pCGivenNotA ∧ w.pCGivenNotA ≤ 1 := by
  simp only [pCGivenNotA, pNotAC]
  have hNotA_pos : 0 < 1 - w.pA := by linarith
  simp only [gt_iff_lt, hNotA_pos, ↓reduceIte]
  constructor
  · apply div_nonneg
    · have : w.pAC ≤ w.pC := le_trans h.2.2.2.2.2.1 (min_le_right w.pA w.pC)
      linarith
    · exact le_of_lt hNotA_pos
  · have hNotAC_le : w.pC - w.pAC ≤ 1 - w.pA := by linarith [h.2.2.2.2.2.2]
    have hNotA_ne : 1 - w.pA ≠ 0 := ne_of_gt hNotA_pos
    calc (w.pC - w.pAC) / (1 - w.pA) ≤ (1 - w.pA) / (1 - w.pA) := by
             apply div_le_div_of_nonneg_right hNotAC_le (le_of_lt hNotA_pos)
         _ = 1 := div_self hNotA_ne

/-- **Law of Total Probability**: P(C) = P(C|A)·P(A) + P(C|¬A)·P(¬A). -/
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

/-- **Bayes' Theorem**: P(A|C) = P(C|A)·P(A) / P(C). -/
theorem bayes_theorem (w : WorldState) (hA : 0 < w.pA) (hC : 0 < w.pC) :
    w.pAGivenC = w.pCGivenA * w.pA / w.pC := by
  simp only [pAGivenC, pCGivenA]
  simp only [gt_iff_lt, hA, hC, ↓reduceIte]
  have hA_ne : w.pA ≠ 0 := ne_of_gt hA
  rw [div_mul_eq_mul_div]
  congr 1
  rw [mul_div_assoc, div_self hA_ne, mul_one]

end WorldState

end Core.CausalBayesNet
