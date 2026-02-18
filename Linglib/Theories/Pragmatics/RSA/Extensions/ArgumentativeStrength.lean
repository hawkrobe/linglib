import Linglib.Theories.Pragmatics.RSA.Extensions.InformationTheory.Basic
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Mathlib.Data.Rat.Defs

/-!
# Argumentative Strength for Quantity Expressions

Merin (1999)'s log-likelihood ratio measure of argumentative strength, as applied
to numerical quantity expressions in Cummins & Franke (2021) and quantifier choice
in Macuch Silva et al. (2024).

## Core Idea

Rather than maximizing informativity (standard RSA), speakers choose quantity
expressions to serve *argumentative goals*: making a conclusion G more or less
credible. The argumentative strength of utterance u for goal G is:

  argStr(u, G) = log₂(P(u|G) / P(u|¬G))     (C&F Eq. 17)

A pragmatic variant replaces literal truth with assertability:

  pragArgStr(u, G) = log₂(P_a(u|G) / P_a(u|¬G))   (C&F Eq. 25)

## Key Results

- Semantic and pragmatic measures can *reverse* the ordering of utterances
- The Bayes factor P(u|G)/P(u|¬G) admits ordinal comparison without log
- argStr is a pointwise KL divergence (bridge to InformationTheory)
- At λ=1 in CombinedUtility, utility reduces to pure argumentative strength

## References

- Merin, A. (1999). Information, relevance, and social decisionmaking.
- Cummins, C. & Franke, M. (2021). Argumentative strength of numerical quantity.
- Macuch Silva, V. et al. (2024). Strategic quantifier use in production.
-/

namespace RSA.ArgumentativeStrength

open RSA.InformationTheory
open RSA.CombinedUtility


-- ============================================================
-- Section 1: Core Definitions (Merin 1999, C&F 2021 §3)
-- ============================================================

/-- An argumentative goal partitions worlds into G (goal-supporting) vs ¬G. -/
structure ArgumentativeGoal (W : Type) where
  /-- Returns true for worlds where the goal holds -/
  goalTrue : W → Bool

/-- Bayes factor: P(u|G) / P(u|¬G), the pre-log ratio.

This is the key quantity for argumentative strength. It measures how much
more likely utterance u is to be true (or assertable) given G vs ¬G.
C&F Eq. 17 (before taking log). -/
def bayesFactor (pGivenG pGivenNotG : ℚ) : ℚ :=
  if pGivenNotG = 0 then
    if pGivenG > 0 then 1000  -- effectively +∞
    else 1  -- 0/0 → neutral
  else pGivenG / pGivenNotG

/-- Argumentative strength: log₂ of the Bayes factor.

argStr(u, G) = log₂(P(u|G) / P(u|¬G))

C&F Eq. 17. Positive values mean u supports G; negative means u supports ¬G. -/
def argStr (pGivenG pGivenNotG : ℚ) : ℚ :=
  log2Approx (bayesFactor pGivenG pGivenNotG)

/-- Pragmatic argumentative strength using assertability probabilities.

pragArgStr(u, G) = log₂(P_a(u|G) / P_a(u|¬G))

C&F Eq. 25. Replaces literal truth with pragmatic assertability. -/
def pragArgStr (pAssertableGivenG pAssertableGivenNotG : ℚ) : ℚ :=
  log2Approx (bayesFactor pAssertableGivenG pAssertableGivenNotG)


-- ============================================================
-- Section 2: Ordinal Characterizations
-- ============================================================

/-- Utterance has positive argumentative strength iff P(u|G) > P(u|¬G).

Ordinal characterization — no log needed. -/
def hasPositiveArgStr (pGivenG pGivenNotG : ℚ) : Prop :=
  pGivenG > pGivenNotG

instance (pGivenG pGivenNotG : ℚ) : Decidable (hasPositiveArgStr pGivenG pGivenNotG) :=
  inferInstanceAs (Decidable (pGivenG > pGivenNotG))

/-- Utterance u₁ is argumentatively stronger than u₂ for goal G iff
its Bayes factor is higher. Ordinal comparison — no log needed. -/
def argumentativelyStronger
    (pGivenG₁ pGivenNotG₁ pGivenG₂ pGivenNotG₂ : ℚ) : Prop :=
  bayesFactor pGivenG₁ pGivenNotG₁ > bayesFactor pGivenG₂ pGivenNotG₂

instance (a b c d : ℚ) : Decidable (argumentativelyStronger a b c d) :=
  inferInstanceAs (Decidable (_ > _))


-- ============================================================
-- Section 3: Difficulty Metric (Macuch Silva et al. 2024)
-- ============================================================

/-- Argumentative difficulty: proportion of truthful states where the strongest
available quantifier is weak. From Macuch Silva et al. (2024).

For a given direction (positive/negative), difficulty measures how hard it is
to frame the state in that direction truthfully. High difficulty → speakers
must use weaker quantifiers. -/
structure ArgumentativeDifficulty where
  /-- Proportion of relevant items (e.g., correct answers out of total) -/
  proportion : ℚ
  /-- Whether the speaker is framing positively or negatively -/
  isPositiveFrame : Bool
  /-- Difficulty value: 0 = easy (can use "all"), 1 = hard (must use "some") -/
  difficulty : ℚ


-- ============================================================
-- Section 4: Rational Hearer (C&F §3.3)
-- ============================================================

/-- Rational hearer (semantic): increase belief in G upon hearing u iff
argStr(u, G) > 0 (C&F Eq. 27). -/
def rationalHearerSemantic (pGivenG pGivenNotG : ℚ) : Bool :=
  decide (hasPositiveArgStr pGivenG pGivenNotG)

/-- Rational hearer (pragmatic): increase belief in G upon hearing u iff
pragArgStr(u, G) > 0 (C&F Eq. 28). -/
def rationalHearerPragmatic (pAssertableGivenG pAssertableGivenNotG : ℚ) : Bool :=
  decide (hasPositiveArgStr pAssertableGivenG pAssertableGivenNotG)


-- ============================================================
-- Section 5: Bridge Theorems
-- ============================================================

/-- argStr is a pointwise KL divergence term.

The KL divergence D_KL(P_G || P_¬G) = Σ_u P_G(u) · log(P_G(u)/P_¬G(u)).
Each summand P_G(u) · log(P_G(u)/P_¬G(u)) contains the argStr as the log factor.
That is, argStr(u, G) = log₂(P(u|G)/P(u|¬G)) is the pointwise divergence. -/
theorem argStr_eq_pointwiseKL (pGivenG pGivenNotG : ℚ)
    (_hG : 0 < pGivenG) (hNotG : 0 < pGivenNotG) :
    argStr pGivenG pGivenNotG =
    log2Approx (pGivenG / pGivenNotG) := by
  unfold argStr bayesFactor
  simp [ne_of_gt hNotG]

/-- Positive argStr iff Bayes factor > 1 (ordinal characterization). -/
theorem argStr_positive_iff (pGivenG pGivenNotG : ℚ)
    (_hG : 0 ≤ pGivenG) (hNotG : 0 < pGivenNotG) :
    hasPositiveArgStr pGivenG pGivenNotG ↔ bayesFactor pGivenG pGivenNotG > 1 := by
  unfold hasPositiveArgStr bayesFactor
  simp [ne_of_gt hNotG]
  constructor
  · exact fun h => lt_div_iff₀ hNotG |>.mpr (by linarith)
  · exact fun h => by have := (lt_div_iff₀ hNotG).mp h; linarith

/-- When λ=1 in CombinedUtility.combined, utility reduces to pure U_B.
If U_B is argumentative strength, this connects combined utility to argStr.

That is: combined 1 U_informative U_argumentative = U_argumentative -/
theorem argStr_from_combined_at_one (utilInformative utilArgumentative : ℚ) :
    combined 1 utilInformative utilArgumentative = utilArgumentative :=
  combined_at_one utilInformative utilArgumentative

/-- A goal-oriented speaker (β > 0) strictly prefers utterances with higher
argumentative strength, connecting Cummins & Franke's argStr ordering to
Barnett et al.'s goal-oriented utility framework.

When U_goal = argStr(u, G), higher argStr → higher goalOrientedUtility. -/
theorem argStr_speaker_prefers_stronger
    (uEpi : ℚ) (argStr₁ argStr₂ : ℚ) (β : ℚ)
    (hβ : 0 < β) (hStr : argStr₁ > argStr₂) :
    goalOrientedUtility uEpi argStr₂ β < goalOrientedUtility uEpi argStr₁ β := by
  unfold goalOrientedUtility
  have : β * argStr₂ < β * argStr₁ := by nlinarith
  linarith

end RSA.ArgumentativeStrength
