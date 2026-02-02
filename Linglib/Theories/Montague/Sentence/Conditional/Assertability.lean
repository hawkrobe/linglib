/-
# Probabilistic Assertability for Conditionals

Assertability conditions for conditional sentences based on conditional probability.

## Key Insight (Grusdt, Lassiter & Franke 2022)

The literal meaning of a conditional "if A then C" is NOT its material implication
truth value, but rather whether P(C|A) exceeds a threshold θ.

This probabilistic semantics:
1. Explains why "If A then C" is odd when A⊥C (missing-link infelicity)
2. Allows RSA to derive conditional perfection as an implicature
3. Connects conditionals to causal/correlational reasoning

## References

- Adams (1975). The Logic of Conditionals.
- Edgington (1995). On Conditionals.
- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals.
-/

import Linglib.Core.CausalBayesNet
import Mathlib.Data.Rat.Defs

namespace Montague.Sentence.Conditional.Assertability

open Core.CausalBayesNet

-- ============================================================================
-- Conditional Probability
-- ============================================================================

/--
Conditional probability P(C|A) = P(A ∧ C) / P(A).

Returns 0 if P(A) = 0 (undefined case).
-/
def conditionalProbability (ws : WorldState) : ℚ :=
  ws.pCGivenA

/--
Conditional probability P(A|C) = P(A ∧ C) / P(C).

Returns 0 if P(C) = 0 (undefined case).
-/
def reversedConditionalProbability (ws : WorldState) : ℚ :=
  ws.pAGivenC

-- ============================================================================
-- Assertability Threshold
-- ============================================================================

/--
The default assertability threshold θ.

A conditional "if A then C" is assertable when P(C|A) > θ.
The paper uses θ = 0.9 as a reasonable default.
-/
def defaultThreshold : ℚ := 9/10

/--
Check if a conditional "if A then C" is assertable given a world state.

A conditional is assertable when:
1. P(A) > 0 (the antecedent is possible)
2. P(C|A) > θ (the conditional probability is high enough)
-/
def assertable (ws : WorldState) (θ : ℚ := defaultThreshold) : Bool :=
  ws.pA > 0 && conditionalProbability ws > θ

/--
Assertability as a rational value for soft semantics.

Returns P(C|A) if P(A) > 0, otherwise 0.
This is useful for RSA models that use soft (graded) semantics.
-/
def assertabilityScore (ws : WorldState) : ℚ :=
  if ws.pA > 0 then conditionalProbability ws else 0

/--
Threshold-based assertability as a rational value.

Returns 1 if assertable, 0 otherwise.
-/
def assertabilityBool (ws : WorldState) (θ : ℚ := defaultThreshold) : ℚ :=
  if assertable ws θ then 1 else 0

-- ============================================================================
-- Contrapositive Assertability
-- ============================================================================

/--
Assertability of the contrapositive: "if ¬C then ¬A".

P(¬A|¬C) = P(¬A ∧ ¬C) / P(¬C)
-/
def contrapositiveProbability (ws : WorldState) : ℚ :=
  let pNotC := 1 - ws.pC
  if pNotC > 0 then ws.pNotANotC / pNotC else 0

/--
Check if the contrapositive "if ¬C then ¬A" is assertable.
-/
def contrapositiveAssertable (ws : WorldState) (θ : ℚ := defaultThreshold) : Bool :=
  ws.pC < 1 && contrapositiveProbability ws > θ

-- ============================================================================
-- Reverse Conditional Assertability
-- ============================================================================

/--
Assertability of the reverse conditional: "if C then A".

P(A|C) = P(A ∧ C) / P(C)

This is relevant for inferring causal direction:
- If "if A then C" is assertable but "if C then A" is not, this suggests A→C
- If both are assertable, this suggests correlation or common cause
-/
def reverseAssertable (ws : WorldState) (θ : ℚ := defaultThreshold) : Bool :=
  ws.pC > 0 && reversedConditionalProbability ws > θ

-- ============================================================================
-- Biconditional Assertability
-- ============================================================================

/--
A biconditional "A iff C" is assertable when both directions are.

This corresponds to strong correlation or deterministic causation.
-/
def biconditionalAssertable (ws : WorldState) (θ : ℚ := defaultThreshold) : Bool :=
  assertable ws θ && reverseAssertable ws θ

-- ============================================================================
-- Missing-Link Detection
-- ============================================================================

/--
Detect "missing-link" cases where the conditional seems odd.

A conditional "if A then C" has a "missing link" when:
1. A and C are (approximately) independent: P(C|A) ≈ P(C)
2. There's no clear causal or correlational connection

This is formalized as: |P(C|A) - P(C)| < ε for some small ε.
-/
def hasMissingLink (ws : WorldState) (ε : ℚ := 1/20) : Bool :=
  if ws.pA > 0 then
    let diff := conditionalProbability ws - ws.pC
    decide (-ε < diff && diff < ε)
  else true  -- If A is impossible, there's no meaningful link

/--
Correlation strength: how much P(C|A) differs from P(C).

Positive values indicate positive correlation.
Negative values indicate negative correlation.
Values near 0 indicate independence (missing link).
-/
def correlationStrength (ws : WorldState) : ℚ :=
  if ws.pA > 0 then conditionalProbability ws - ws.pC else 0

-- ============================================================================
-- Causal Inference from Assertability
-- ============================================================================

/--
Asymmetry score: how much more assertable is "if A then C" than "if C then A"?

Large positive values suggest A→C causal direction.
Large negative values suggest C→A causal direction.
Values near 0 suggest independence or bidirectional causation.
-/
def asymmetryScore (ws : WorldState) : ℚ :=
  assertabilityScore ws - reversedConditionalProbability ws

/--
Infer the most likely causal relation based on conditional assertability patterns.

Heuristic:
- If "if A then C" is assertable but "if C then A" is not: likely A→C
- If "if C then A" is assertable but "if A then C" is not: likely C→A
- If both or neither are assertable: likely independent or common cause
-/
def inferCausalRelation (ws : WorldState) (θ : ℚ := defaultThreshold)
    : CausalRelation :=
  let fwdAssert := assertable ws θ
  let bwdAssert := reverseAssertable ws θ
  if fwdAssert && !bwdAssert then .ACausesC
  else if !fwdAssert && bwdAssert then .CCausesA
  else .Independent

-- ============================================================================
-- Connection to RSA
-- ============================================================================

/--
The key connection to RSA: the literal listener L0 interprets a conditional
by sampling world states where the conditional is assertable.

This function provides the "agreement" score φ for RSA:
- Returns 1 if the conditional is assertable in the world state
- Returns 0 otherwise

For soft semantics, use `assertabilityScore` instead.
-/
def conditionalSemantics (ws : WorldState) (θ : ℚ := defaultThreshold) : ℚ :=
  assertabilityBool ws θ

/--
Soft semantics: the agreement is the conditional probability itself.

This allows the RSA model to reason about degrees of assertability.
-/
def softConditionalSemantics (ws : WorldState) : ℚ :=
  assertabilityScore ws

-- ============================================================================
-- Theorems
-- ============================================================================

/--
If P(A) = 0, the conditional is not assertable (antecedent impossible).
-/
theorem not_assertable_if_antecedent_impossible (ws : WorldState) (θ : ℚ)
    (h : ws.pA = 0) : assertable ws θ = false := by
  simp [assertable, h]

/--
Assertability implies the antecedent is possible.
-/
theorem assertable_implies_antecedent_possible (ws : WorldState) (θ : ℚ)
    (h : assertable ws θ = true) : ws.pA > 0 := by
  simp [assertable] at h
  exact h.1

end Montague.Sentence.Conditional.Assertability
