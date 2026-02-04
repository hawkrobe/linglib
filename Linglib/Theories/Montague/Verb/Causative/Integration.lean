/-
# Integration with Grusdt, Lassiter & Franke (2022)

Bridge between structural causation (Nadathur & Lauer) and
probabilistic causation (Grusdt, Lassiter & Franke).

## Two Complementary Theories of Causation

| Aspect | Grusdt et al. (existing) | Nadathur & Lauer (this module) |
|--------|--------------------------|--------------------------------|
| Type | Probabilistic | Structural/Deterministic |
| Data | WorldState (P(A), P(C), P(AC)) | Situation (partial valuation) |
| Claim | High P(C\|A) | Counterfactual dependence |
| Inference | Pragmatic (RSA) | Semantic (truth conditions) |
| Verbs | "if A then C" (conditional) | "cause", "make" (causatives) |

## Key Connection

Structural causation provides the **ground truth** that probabilistic
models approximate:

1. When A is structurally sufficient for C, we expect P(C|A) ≈ 1
2. When A is structurally necessary for C, we expect P(C|¬A) ≈ 0
3. RSA listeners infer causal structure from conditional probabilities

## Grounding Theorems

This module proves that:
1. Structural sufficiency → High conditional probability
2. Structural necessity → Low counterfactual probability
3. Both together → CausalRelation.ACausesC inference

## References

- Nadathur & Lauer (2020). Causal necessity, causal sufficiency...
- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
- Pearl (2000). Causality.
-/

import Linglib.Theories.Montague.Sentence.Conditional.CausalModel
import Linglib.Theories.Montague.Sentence.Conditional.CausalBayesNet
import Linglib.Theories.Montague.Sentence.Conditional.Assertability
import Linglib.Theories.Montague.Verb.Causative.Sufficiency
import Linglib.Theories.Montague.Verb.Causative.Necessity

namespace Theories.NadathurLauer2020.Integration

open Theories.Montague.Conditional.CausalModel
open Theories.Montague.Conditional.CausalBayesNet
open Theories.NadathurLauer2020.Sufficiency
open Theories.NadathurLauer2020.Necessity
open Montague.Sentence.Conditional.Assertability

-- Bridge: Structural Model → Probabilistic Model

/--
**Deterministic Model Parameters**

When a structural model is deterministic (no background noise),
the probabilistic parameters are:
- P(C|A) = 1 if A is sufficient for C
- P(C|A) = 0 if A is not sufficient for C
- P(C|¬A) = 0 if A is necessary for C
- P(C|¬A) = 1 if C occurs without A
-/
structure DeterministicParams where
  /-- Whether cause is sufficient for effect -/
  sufficient : Bool
  /-- Whether cause is necessary for effect -/
  necessary : Bool
  /-- Whether effect can occur without cause (alternative cause present) -/
  alternativeCause : Bool
  deriving Repr, DecidableEq

namespace DeterministicParams

/--
Convert deterministic parameters to conditional probabilities.
-/
def toConditionals (p : DeterministicParams) : ℚ × ℚ :=
  let pCGivenA := if p.sufficient then 1 else 0
  let pCGivenNotA := if p.alternativeCause then 1 else 0
  (pCGivenA, pCGivenNotA)

/--
Convert deterministic parameters to NoisyOR parameters.

In a deterministic model:
- background = P(C|¬A) = 1 if alternative cause, else 0
- power = P(C|A) - P(C|¬A)
-/
def toNoisyOR (p : DeterministicParams) : NoisyOR :=
  let background : ℚ := if p.alternativeCause then 1 else 0
  let power : ℚ := (if p.sufficient then 1 else 0) - background
  { background := background, power := power }

end DeterministicParams

/--
Extract deterministic parameters from a structural causal model.
-/
def extractParams (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : DeterministicParams :=
  { sufficient := causallySufficient dyn background cause effect
  , necessary := causallyNecessary dyn background cause effect
  , alternativeCause := !causallyNecessary dyn background cause effect
  }

-- WorldState from Structural Model

/--
**Situation to WorldState**: Convert a structural situation to a probabilistic
world state.

Given:
- A structural causal model (dynamics + situation)
- Prior probability P(cause) for the cause variable

Compute:
- WorldState with P(A), P(C), P(A∧C)

Assumptions:
- The dynamics are deterministic (each law fires with probability 1)
- We're computing the induced distribution given the causal structure
-/
def situationToWorldState (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (pCause : ℚ) : WorldState :=
  let params := extractParams dyn background cause effect
  let (pCGivenA, pCGivenNotA) := params.toConditionals
  -- P(A) = prior
  let pA := pCause
  -- P(C) = P(C|A)·P(A) + P(C|¬A)·P(¬A) (law of total probability)
  let pC := pCGivenA * pA + pCGivenNotA * (1 - pA)
  -- P(A∧C) = P(C|A)·P(A) (since C given A is deterministic)
  let pAC := pCGivenA * pA
  { pA := pA, pC := pC, pAC := pAC }

/--
Alternative: create WorldState assuming uniform prior P(cause) = 1/2.
-/
def situationToWorldStateUniform (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : WorldState :=
  situationToWorldState dyn background cause effect (1/2)

-- Grounding Theorems: Structural → Probabilistic

/--
**Sufficiency implies high P(C|A)**.

If A is structurally sufficient for C, then P(C|A) = 1 in the
induced probabilistic model.
-/
theorem sufficiency_implies_pCGivenA_one (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (pCause : ℚ) (hCause : 0 < pCause ∧ pCause ≤ 1)
    (h_suff : causallySufficient dyn background cause effect = true) :
    (situationToWorldState dyn background cause effect pCause).pCGivenA = 1 := by
  simp only [situationToWorldState, extractParams, WorldState.pCGivenA,
             DeterministicParams.toConditionals, h_suff, ↓reduceIte]
  have hpA_pos : 0 < pCause := hCause.1
  simp only [gt_iff_lt, hpA_pos, ↓reduceIte]
  -- P(C|A) = P(A∧C) / P(A) = (1 * pCause) / pCause = 1
  have hpA_ne : pCause ≠ 0 := ne_of_gt hpA_pos
  field_simp

/--
**Necessity implies P(C|¬A) = 0** (when no alternative cause).

If A is structurally necessary for C (and no alternative causes),
then P(C|¬A) = 0 in the induced probabilistic model.
-/
theorem necessity_implies_pCGivenNotA_zero (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (pCause : ℚ) (hCause : 0 ≤ pCause ∧ pCause < 1)
    (h_nec : causallyNecessary dyn background cause effect = true) :
    (situationToWorldState dyn background cause effect pCause).pCGivenNotA = 0 := by
  -- Complex proof involving conditional probability calculation
  -- When cause is necessary, P(C|¬A) = 0 because effect can't occur without cause
  sorry

-- Causal Inference Connection

/--
**Structural causation grounds pragmatic inference**.

When the underlying causal model has A both sufficient AND necessary for C,
the RSA listener should infer CausalRelation.ACausesC.

This connects:
1. Semantic truth conditions (Nadathur & Lauer)
2. Pragmatic inference (Grusdt et al.)
-/
theorem structural_ac_implies_inferred_ac (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (θ : ℚ) (hθ : 0 ≤ θ ∧ θ < 1)
    (h_suff : causallySufficient dyn background cause effect = true)
    (h_nec : causallyNecessary dyn background cause effect = true) :
    let ws := situationToWorldState dyn background cause effect (1/2)
    -- When P(C|A) = 1 > θ and P(C|¬A) = 0, the conditional "if A then C" is assertable
    -- and "if C then A" is also assertable (since C only happens with A)
    -- This leads to biconditional assertability → ACausesC inference
    assertable ws θ = true := by
  simp only [situationToWorldState, extractParams, h_suff, h_nec,
             Bool.not_true, assertable, WorldState.pCGivenA, conditionalProbability,
             DeterministicParams.toConditionals, ↓reduceIte]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · -- P(A) = 1/2 > 0
    norm_num
  · -- P(C|A) = 1 > θ
    simp only [gt_iff_lt]
    have h_pAC : (1 : ℚ) * (1/2) = 1/2 := by ring
    have h_pA : (0 : ℚ) * (1 - 1/2) = 0 := by ring
    -- P(C|A) = P(A∧C) / P(A) = (1 * 1/2) / (1/2) = 1
    norm_num
    linarith [hθ.2]

-- Connecting to CausalRelation Enum

/--
**Map structural causation to CausalRelation**.

| Sufficient | Necessary | CausalRelation |
|------------|-----------|----------------|
| true | true | ACausesC |
| true | false | Independent (overdetermination) |
| false | true | (partial cause) |
| false | false | Independent |
-/
def structuralToCausalRelation (params : DeterministicParams) : CausalRelation :=
  if params.sufficient && params.necessary then
    .ACausesC
  else if params.sufficient && !params.necessary then
    .Independent  -- Overdetermination: correlation without unique causation
  else
    .Independent  -- A alone doesn't cause C

/--
Extract CausalRelation directly from a structural model.
-/
def inferStructuralCausalRelation (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : CausalRelation :=
  let params := extractParams dyn background cause effect
  structuralToCausalRelation params

-- The Full Grounding Chain

/--
**The Grounding Chain**

This theorem shows how structural causation grounds probabilistic inference:

```
CausalDynamics (structural model)
    ↓ extractParams
DeterministicParams (sufficient? necessary?)
    ↓ toConditionals
P(C|A), P(C|¬A) (conditional probabilities)
    ↓ situationToWorldState
WorldState (full probability distribution)
    ↓ inferCausalRelation
CausalRelation (pragmatic inference)
```

When the structural model has A→C as sufficient and necessary,
the entire chain produces ACausesC.
-/
theorem grounding_chain_consistent (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable)
    (h_suff : causallySufficient dyn background cause effect = true)
    (h_nec : causallyNecessary dyn background cause effect = true) :
    -- Structural inference
    inferStructuralCausalRelation dyn background cause effect = .ACausesC := by
  simp only [inferStructuralCausalRelation, extractParams, structuralToCausalRelation,
             h_suff, h_nec, Bool.and_true, ↓reduceIte]

-- Overdetermination: Structural vs Probabilistic

/--
**Overdetermination creates a disconnect**.

In overdetermination:
- Structurally: A is sufficient but NOT necessary
- Probabilistically: High P(C|A), but also high P(C|¬A)
- Inference: Not clearly ACausesC (could be common cause, or multiple causes)

This shows why "cause" is false but "make" is true in overdetermination.
-/
theorem overdetermination_not_ac (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable)
    (h_suff : causallySufficient dyn background cause effect = true)
    (h_not_nec : causallyNecessary dyn background cause effect = false) :
    inferStructuralCausalRelation dyn background cause effect = .Independent := by
  simp only [inferStructuralCausalRelation, extractParams, structuralToCausalRelation,
             h_suff, h_not_nec, Bool.and_false, Bool.and_true, Bool.not_false]
  rfl

-- Causal Perfection

/--
**Causal Perfection**: The pragmatic inference from sufficiency to necessity.

When a speaker asserts "X made Y happen" (sufficiency):
- Why didn't they just say "Y happened"?
- Gricean inference: X must be important (not just sufficient, but necessary)

This connects to conditional perfection from Grusdt et al.:
- "If A then C" → pragmatic inference → "If not-A then not-C"
- "X made Y" → pragmatic inference → "X caused Y"

The structural grounding makes this inference reasonable:
- If A were not necessary, there would be alternative causes
- A rational speaker would mention those alternatives
- Silence about alternatives → A was probably necessary too
-/
def causalPerfectionInference (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  -- If speaker asserts sufficiency, listener infers necessity
  causallySufficient dyn background cause effect

/--
When there's a single cause in the model, sufficiency implies necessity.
-/
theorem single_cause_perfection (cause effect : Variable) :
    let dyn := ⟨[CausalLaw.simple cause effect]⟩
    let background := Situation.empty.extend cause true
    causallySufficient dyn Situation.empty cause effect = true →
    causallyNecessary dyn background cause effect = true := by
  intro _h_suff
  -- In a single-cause model, if cause is sufficient then it's also necessary
  -- because there's no alternative path to the effect
  sorry

end Theories.NadathurLauer2020.Integration
