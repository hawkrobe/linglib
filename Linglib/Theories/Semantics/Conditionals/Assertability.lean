/-
# Probabilistic Assertability for Conditionals

Assertability conditions for conditional sentences based on conditional probability.

## Insight (Grusdt, Lassiter & Franke 2022)

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

import Linglib.Core.Causation
import Mathlib.Data.Rat.Defs

namespace Semantics.Conditionals.Assertability

open Core.Causation

-- Conditional Probability

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

-- Assertability Threshold

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

-- Contrapositive Assertability

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

-- Reverse Conditional Assertability

/--
Assertability of the reverse conditional: "if C then A".

P(A|C) = P(A ∧ C) / P(C)

This is relevant for inferring causal direction:
- If "if A then C" is assertable but "if C then A" is not, this suggests A→C
- If both are assertable, this suggests correlation or common cause
-/
def reverseAssertable (ws : WorldState) (θ : ℚ := defaultThreshold) : Bool :=
  ws.pC > 0 && reversedConditionalProbability ws > θ

-- Biconditional Assertability

/--
A biconditional "A iff C" is assertable when both directions are.

This corresponds to strong correlation or deterministic causation.
-/
def biconditionalAssertable (ws : WorldState) (θ : ℚ := defaultThreshold) : Bool :=
  assertable ws θ && reverseAssertable ws θ

-- Missing-Link Detection

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

-- Causal Inference from Assertability

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

-- Connection to RSA

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

-- Theorems

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

/--
**Assertability is monotone in threshold** (lower threshold → more assertable).

If a conditional is assertable at threshold θ₂, it is also assertable at any lower threshold θ₁ ≤ θ₂.
-/
theorem assertability_monotone (ws : WorldState) (θ₁ θ₂ : ℚ) :
    θ₁ ≤ θ₂ → assertable ws θ₂ = true → assertable ws θ₁ = true := by
  intro h_le h_assert
  simp only [assertable, Bool.and_eq_true, decide_eq_true_eq] at *
  constructor
  · exact h_assert.1
  · calc conditionalProbability ws > θ₂ := h_assert.2
         _ ≥ θ₁ := h_le

/--
**Assertability score is bounded** in [0, 1].

The assertability score (conditional probability when defined) is always between 0 and 1.
-/
theorem assertability_score_bounded (ws : WorldState) (h : ws.IsValid) :
    0 ≤ assertabilityScore ws ∧ assertabilityScore ws ≤ 1 := by
  simp only [assertabilityScore]
  split
  · -- Case: ws.pA > 0
    have hA : 0 < ws.pA := by assumption
    simp only [conditionalProbability]
    exact WorldState.valid_implies_pCGivenA_bounded ws h hA
  · -- Case: ws.pA ≤ 0
    exact ⟨le_refl 0, zero_le_one⟩

/--
**Conditional probability is bounded** when the antecedent is possible.
-/
theorem conditional_probability_bounded (ws : WorldState) (h : ws.IsValid) (hA : 0 < ws.pA) :
    0 ≤ conditionalProbability ws ∧ conditionalProbability ws ≤ 1 := by
  simp only [conditionalProbability]
  exact WorldState.valid_implies_pCGivenA_bounded ws h hA

-- Missing-Link Characterization

/--
**Missing-link iff weak correlation**.

A conditional has a missing link iff the correlation strength is within ε of 0.
This is a bidirectional characterization when P(A) > 0.
-/
theorem missing_link_iff_weak_correlation (ws : WorldState) (ε : ℚ) (hA : 0 < ws.pA) :
    hasMissingLink ws ε = true ↔ -ε < correlationStrength ws ∧ correlationStrength ws < ε := by
  simp only [hasMissingLink, correlationStrength, hA, ↓reduceIte,
             conditionalProbability, Bool.and_eq_true, decide_eq_true_eq]

/--
**Independence implies missing link**.

If A and C are probabilistically independent (P(A∧C) = P(A)·P(C)),
then the conditional has a missing link (for any positive ε).
-/
theorem independent_implies_missing_link (ws : WorldState) (ε : ℚ) (hε : 0 < ε)
    (hA : 0 < ws.pA) (h_indep : ws.pAC = ws.pA * ws.pC) :
    hasMissingLink ws ε = true := by
  rw [missing_link_iff_weak_correlation ws ε hA]
  simp only [correlationStrength, hA, ↓reduceIte, conditionalProbability, WorldState.pCGivenA]
  -- P(C|A) - P(C) = P(AC)/P(A) - P(C) = (P(A)·P(C))/P(A) - P(C) = P(C) - P(C) = 0
  have hA_ne : ws.pA ≠ 0 := ne_of_gt hA
  have h_eq : ws.pAC / ws.pA - ws.pC = 0 := by
    rw [h_indep, mul_comm, mul_div_assoc, div_self hA_ne, mul_one, sub_self]
  rw [h_eq]
  exact ⟨by linarith, by linarith⟩

/--
**Missing link means no correlation boost**.

If there's a missing link, then P(C|A) ≈ P(C), meaning knowing A doesn't
significantly change the probability of C.
-/
theorem missing_link_no_boost (ws : WorldState) (ε : ℚ) (hA : 0 < ws.pA) :
    hasMissingLink ws ε = true →
    conditionalProbability ws - ε < ws.pC ∧ ws.pC < conditionalProbability ws + ε := by
  rw [missing_link_iff_weak_correlation ws ε hA]
  simp only [correlationStrength, hA, ↓reduceIte, conditionalProbability]
  intro ⟨h1, h2⟩
  exact ⟨by linarith, by linarith⟩

/--
**Correlation strength is zero iff independence**.

When P(A) > 0, correlation strength is exactly 0 iff A and C are independent.
-/
theorem correlation_strength_zero_iff_independent (ws : WorldState) (hA : 0 < ws.pA) :
    correlationStrength ws = 0 ↔ ws.pAC = ws.pA * ws.pC := by
  simp only [correlationStrength, hA, ↓reduceIte, conditionalProbability,
             WorldState.pCGivenA, sub_eq_zero]
  have hA_ne : ws.pA ≠ 0 := ne_of_gt hA
  constructor
  · intro h
    -- h : ws.pAC / ws.pA = ws.pC
    rw [div_eq_iff hA_ne] at h
    linarith
  · intro h
    -- h : ws.pAC = ws.pA * ws.pC
    rw [h, mul_comm, mul_div_assoc, div_self hA_ne, mul_one]

end Semantics.Conditionals.Assertability
