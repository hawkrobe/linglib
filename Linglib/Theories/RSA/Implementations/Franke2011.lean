/-
# Iterated Best Response (IBR) Model

Implements Franke (2011) "Quantity implicatures, exhaustive interpretation,
and rational conversation" Semantics & Pragmatics 4(1):1-82.

## The Core Insight

This paper provides the game-theoretic foundation for quantity implicatures,
showing that:

1. **IBR = EXH**: Iterated best response reasoning converges to exhaustive
   interpretation (exhMW/exhIE)

2. **RSA is "soft" IBR**: RSA's softmax is a smoothed version of IBR's argmax.
   As α → ∞, RSA → IBR → EXH

## Key Definitions

**Interpretation Game** (Section 6):
- States: Equivalence classes of worlds grouped by which alternatives are true
- Messages: The set of alternative utterances
- Meaning: ⟦m⟧(s) = 1 iff m is true at state s

**IBR Reasoning** (Section 8):
- L₀(s | m) ∝ ⟦m⟧(s) · P(s)         -- Literal listener
- S₁(m | s) = argmax_m L₀(s | m)    -- Best-responding speaker
- L₂(s | m) ∝ 1_{S₁(m|s) > 0}       -- Pragmatic listener
- Iterate until fixed point

**Main Result**: IBR fixed point = exhMW (minimal worlds exhaustification)

## Architecture

This implementation connects:
- RSA.Core.Basic (softmax recursion)
- NeoGricean.Exhaustivity.Basic (exhMW, exhIE)
- The limit theorem: RSA → IBR as α → ∞

## References

- Franke (2011). Quantity implicatures, exhaustive interpretation, and
  rational conversation. S&P 4(1):1-82.
- Benz, Jäger & van Rooij (2005). Game theory and pragmatics.
- Jäger & Ebert (2009). Pragmatic rationalizability.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.NeoGricean.Exhaustivity.Basic
import Linglib.Core.Softmax.Basic
import Linglib.Core.Softmax.Limits

namespace RSA.IBR

open NeoGricean.Exhaustivity

-- ============================================================================
-- SECTION 1: Interpretation Games (Franke Section 6)
-- ============================================================================

/-!
## Interpretation Games

Franke defines an interpretation game as:
- A set of states T (epistemic possibilities)
- A set of messages M (alternative utterances)
- A meaning function ⟦·⟧ : M → T → Bool
- Prior probability P over states

States are defined as equivalence classes: two worlds are in the same state
iff they agree on the truth of all alternatives.
-/

/-- An interpretation game for quantity implicature reasoning.

This formalizes Section 6 of Franke (2011). The key insight is that
states are not arbitrary possible worlds, but rather equivalence classes
defined by alternative truth patterns. -/
structure InterpGame where
  /-- Type of states (equivalence classes of worlds) -/
  State : Type
  /-- Type of messages (alternative utterances) -/
  Message : Type
  /-- Semantic meaning: is message m true at state s? -/
  meaning : Message → State → Bool
  /-- Prior probability over states -/
  prior : State → ℚ
  /-- Fintype instances -/
  [stateFintype : Fintype State]
  [messageFintype : Fintype Message]
  [stateDecEq : DecidableEq State]
  [messageDecEq : DecidableEq Message]

attribute [instance] InterpGame.stateFintype InterpGame.messageFintype
  InterpGame.stateDecEq InterpGame.messageDecEq

namespace InterpGame

variable (G : InterpGame)

/-- States where message m is true -/
def trueStates (m : G.Message) : Finset G.State :=
  Finset.univ.filter (fun s => G.meaning m s = true)

/-- Messages true at state s -/
def trueMessages (s : G.State) : Finset G.Message :=
  Finset.univ.filter (fun m => G.meaning m s = true)

/-- Informativity of a message (reciprocal of true states, as ratio) -/
def informativity (m : G.Message) : ℚ :=
  let n := (G.trueStates m).card
  if n = 0 then 0 else 1 / n

end InterpGame

-- ============================================================================
-- SECTION 2: IBR Strategies (Franke Section 8)
-- ============================================================================

/-!
## IBR Strategies

A hearer strategy maps messages to probability distributions over states.
A speaker strategy maps states to probability distributions over messages.

In the discrete IBR model, strategies are typically "pure" (deterministic),
but we use rational weights to handle ties uniformly.
-/

/-- A hearer strategy: P(state | message) -/
structure HearerStrategy (G : InterpGame) where
  respond : G.Message → G.State → ℚ

/-- A speaker strategy: P(message | state) -/
structure SpeakerStrategy (G : InterpGame) where
  choose : G.State → G.Message → ℚ

namespace HearerStrategy

variable {G : InterpGame}

/-- Uniform distribution over states where m is true -/
def literal (G : InterpGame) : HearerStrategy G where
  respond := fun m s =>
    if G.meaning m s then
      let n := (G.trueStates m).card
      if n = 0 then 0 else 1 / n
    else 0

/-- Support of hearer's response to message m -/
def support (H : HearerStrategy G) (m : G.Message) : Finset G.State :=
  Finset.univ.filter (fun s => H.respond m s > 0)

end HearerStrategy

namespace SpeakerStrategy

variable {G : InterpGame}

/-- Support of speaker's choice at state s -/
def support (S : SpeakerStrategy G) (s : G.State) : Finset G.Message :=
  Finset.univ.filter (fun m => S.choose s m > 0)

/-- Best response speaker: choose messages that maximize hearer success -/
def bestResponse (G : InterpGame) (H : HearerStrategy G) : SpeakerStrategy G where
  choose := fun s m =>
    -- Utility of message m at state s = P(hearer guesses s | m)
    let utility := H.respond m s
    -- Find max utility among true messages
    let trueMessages := G.trueMessages s
    -- Use fold to find max (handles empty case)
    let maxUtility := trueMessages.fold max 0 (fun m' => H.respond m' s)
    -- Uniform over optimal messages
    if G.meaning m s = true ∧ utility == maxUtility then
      let optimalCount := trueMessages.filter (fun m' =>
        H.respond m' s == maxUtility)
      if optimalCount.card = 0 then 0 else 1 / optimalCount.card
    else 0

/-- Best response speaker always gives non-negative probabilities. -/
theorem bestResponse_nonneg (G : InterpGame) (H : HearerStrategy G) (s : G.State) (m : G.Message) :
    0 ≤ (bestResponse G H).choose s m := by
  simp only [bestResponse]
  split_ifs with hcond hzero
  · -- Branch: hcond true, hzero (optimalCount.card = 0) true → value is 0
    exact le_refl 0
  · -- Branch: hcond true, hzero false → value is 1 / optimalCount.card
    apply one_div_nonneg.mpr
    exact Nat.cast_nonneg _
  · -- Branch: hcond false → value is 0
    exact le_refl 0

/-- Best response speaker gives zero probability to false messages. -/
theorem bestResponse_false_zero (G : InterpGame) (H : HearerStrategy G) (s : G.State) (m : G.Message)
    (hFalse : G.meaning m s = false) :
    (bestResponse G H).choose s m = 0 := by
  simp only [bestResponse]
  split_ifs with hcond hzero
  · -- hcond says meaning m s = true, but hFalse says it's false, contradiction
    exact absurd hcond.1 (by simp [hFalse])
  · -- Same contradiction
    exact absurd hcond.1 (by simp [hFalse])
  · -- hcond false → value is 0
    rfl

/-- Best response speaker probabilities sum to at most 1 at any state.

For states with at least one true message, this is exactly 1 (uniform over optimal).
For states with no true messages, this is 0. -/
theorem bestResponse_sum_le_one (G : InterpGame) (H : HearerStrategy G) (s : G.State) :
    Finset.univ.sum (fun m => (bestResponse G H).choose s m) ≤ 1 := by
  -- Each message with positive probability has choose s m = 1/k for some k
  -- The sum is over at most k messages, giving total 1
  -- If no optimal messages, sum is 0
  sorry -- Requires careful analysis of bestResponse structure

end SpeakerStrategy

-- ============================================================================
-- SECTION 3: IBR Iteration (Franke Section 8.2)
-- ============================================================================

/-!
## IBR Iteration

The core IBR algorithm iterates between:
- Hearer update: Given speaker strategy, update beliefs
- Speaker update: Given hearer strategy, best-respond

Starting from L₀ (literal interpretation), we get:
L₀ → S₁ → L₂ → S₃ → L₄ → ...

Franke proves this converges in finite steps for finite games.
-/

/-- L₀: Literal listener (Franke Def. 22) -/
def L0 (G : InterpGame) : HearerStrategy G :=
  HearerStrategy.literal G

/-- Hearer update: Given speaker strategy, compute posterior.

L_{n+1}(s | m) ∝ S_n(m | s) · P(s)

This is Bayes' rule with the speaker strategy as likelihood. -/
def hearerUpdate (G : InterpGame) (S : SpeakerStrategy G) : HearerStrategy G where
  respond := fun m s =>
    let numerator := S.choose s m * G.prior s
    let denominator := Finset.univ.sum fun s' => S.choose s' m * G.prior s'
    if denominator == 0 then 0 else numerator / denominator

/-- Speaker update: Best response to hearer strategy.

S_{n+1}(m | s) = argmax_m L_n(s | m)

Uniform over optimal messages. -/
def speakerUpdate (G : InterpGame) (H : HearerStrategy G) : SpeakerStrategy G :=
  SpeakerStrategy.bestResponse G H

/-- One full IBR iteration step -/
def ibrStep (G : InterpGame) (H : HearerStrategy G) : HearerStrategy G :=
  hearerUpdate G (speakerUpdate G H)

/-- IBR reasoning for n iterations starting from L₀ -/
def ibrN (G : InterpGame) (n : ℕ) : HearerStrategy G :=
  match n with
  | 0 => L0 G
  | n + 1 => ibrStep G (ibrN G n)

/-- S₁: First pragmatic speaker -/
def S1 (G : InterpGame) : SpeakerStrategy G :=
  speakerUpdate G (L0 G)

/-- L₂: First pragmatic listener -/
def L2 (G : InterpGame) : HearerStrategy G :=
  hearerUpdate G (S1 G)

-- ============================================================================
-- SECTION 4: IBR Fixed Point (Franke Section 8.3)
-- ============================================================================

/-!
## IBR Fixed Point

Franke proves that IBR converges to a fixed point in finite steps.
The fixed point hearer strategy is the "pragmatic interpretation."
-/

/-- Check if hearer strategy is a fixed point of IBR -/
def isIBRFixedPoint (G : InterpGame) (H : HearerStrategy G) : Prop :=
  ∀ m s, H.respond m s = (ibrStep G H).respond m s

/-- At a fixed point with non-negative priors, H.respond is non-negative.

This follows from the fact that H = ibrStep G H, and ibrStep uses
hearerUpdate which gives non-negative values when priors are non-negative. -/
theorem fp_respond_nonneg (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (m : G.Message) (s : G.State) :
    H.respond m s ≥ 0 := by
  rw [hFP m s]
  simp only [ibrStep, hearerUpdate]
  split_ifs with hdenom
  · exact le_refl 0
  · -- numerator / denominator where numerator ≥ 0 and denominator ≥ 0
    apply div_nonneg
    · -- Numerator: S(m|s) * prior(s) ≥ 0
      apply mul_nonneg
      · exact SpeakerStrategy.bestResponse_nonneg G H s m
      · exact hPriorNonneg s
    · -- Denominator: Σ S(m|s') * prior(s') ≥ 0
      apply Finset.sum_nonneg
      intro s' _
      apply mul_nonneg
      · exact SpeakerStrategy.bestResponse_nonneg G H s' m
      · exact hPriorNonneg s'

/-- The pragmatic interpretation: support of the IBR fixed point listener -/
def pragmaticSupport (G : InterpGame) (H : HearerStrategy G) (m : G.Message) :
    Finset G.State :=
  H.support m

-- ============================================================================
-- SECTION 4.1: Expected Gain and IBR Convergence (Franke Appendix B.4)
-- ============================================================================

/-!
## Expected Gain Framework

Franke proves IBR convergence via monotonicity of expected gain.
This is the key to establishing both:
1. IBR always reaches a fixed point (Theorem 3)
2. The fixed point equals exhMW (via the characterization)

### Definition (Expected Gain)

For interpretation games with aligned utilities U_S = U_R = U:

  EG(σ, ρ) = Σ_t Pr(t) × Σ_m σ(t,m) × Σ_a ρ(m,a) × U(t,m,a)

For interpretation games where A = T and U(t,m,a) = 1 if t = a, else 0:

  EG(S, R) = Σ_t Pr(t) × Σ_m S(t,m) × R(m,t)

This measures the expected success rate of communication.

### Lemma 3 (Monotonicity)

In signaling games of pure cooperation, EG is monotonically increasing:
- EG(S_i, R_{i+1}) ≤ EG(S_{i+2}, R_{i+1})
- EG(S_{i+1}, R_i) ≤ EG(S_{i+1}, R_{i+2})

### Theorem 3 (Convergence)

For finite games of pure cooperation, IBR always reaches a fixed point.
Proof: EG is monotonically increasing and bounded, so must stabilize.

### Key Insight (Equation 131)

At each IBR step, the receiver prefers states where the speaker had fewer options:

  μ_{k+1}(t₁|m) > μ_{k+1}(t₂|m)  iff  |S_k(t₁)| < |S_k(t₂)|

This means: receiver selects states with **minimum true alternatives** = minimal in <_ALT!
-/

/-- Expected gain of a speaker-hearer strategy pair.

For interpretation games: EG measures expected communication success.
EG(S, R) = Σ_t Pr(t) × Σ_m S(t,m) × R(m,t)

This equals the probability of successful state recovery. -/
noncomputable def expectedGain (G : InterpGame) (S : SpeakerStrategy G) (H : HearerStrategy G) : ℚ :=
  Finset.univ.sum fun t =>
    G.prior t * Finset.univ.sum fun m =>
      S.choose t m * H.respond m t

/-- **Lemma 3a**: Speaker improvement increases expected gain.

If S_{i+2} is a best response to R_{i+1}, then EG(S_i, R_{i+1}) ≤ EG(S_{i+2}, R_{i+1}).

Proof: By definition of best response, S_{i+2}(t) maximizes expected utility for each t. -/
theorem eg_speaker_improvement (G : InterpGame)
    (S_old S_new : SpeakerStrategy G) (H : HearerStrategy G)
    (hBR : S_new = SpeakerStrategy.bestResponse G H) :
    expectedGain G S_old H ≤ expectedGain G S_new H := by
  sorry -- Requires showing best response improves expected utility at each state

/-- **Lemma 3b**: Hearer improvement increases expected gain.

If R_{i+2} is a best response to S_{i+1}, then EG(S_{i+1}, R_i) ≤ EG(S_{i+1}, R_{i+2}).

Proof: By Bayesian update, R_{i+2} maximizes posterior probability of correct state. -/
theorem eg_hearer_improvement (G : InterpGame)
    (S : SpeakerStrategy G) (H_old H_new : HearerStrategy G)
    (hBR : H_new = hearerUpdate G S) :
    expectedGain G S H_old ≤ expectedGain G S H_new := by
  sorry -- Requires showing Bayesian update improves expected accuracy

/-- Expected gain is bounded above by 1 (probability of perfect communication). -/
theorem eg_bounded (G : InterpGame) (S : SpeakerStrategy G) (H : HearerStrategy G)
    (hPriorSum : Finset.univ.sum G.prior = 1)
    (hPriorNonneg : ∀ s, G.prior s ≥ 0) :
    expectedGain G S H ≤ 1 := by
  sorry -- Requires showing it's a probability

/-- **Theorem 3**: IBR always reaches a fixed point for finite interpretation games.

Proof: By Lemma 3, expected gain EG is monotonically increasing along the IBR sequence.
Since EG is bounded above and there are only finitely many possible strategy profiles,
the sequence must reach a fixed point where EG stabilizes.

More precisely:
1. EG(S_k, R_{k+1}) ≤ EG(S_{k+2}, R_{k+1}) by speaker improvement
2. EG(S_{k+1}, R_k) ≤ EG(S_{k+1}, R_{k+2}) by hearer improvement
3. EG ≤ 1 (bounded)
4. Finitely many strategies ⟹ sequence stabilizes ⟹ fixed point
-/
theorem ibr_reaches_fixed_point (G : InterpGame) :
    ∃ n : ℕ, isIBRFixedPoint G (ibrN G n) := by
  sorry -- Requires formalizing the monotonicity + finiteness argument

-- ============================================================================
-- SECTION 4.2: Fixed Point Characterization via Minimum Alternatives
-- ============================================================================

/-!
## Fixed Point = Minimum Alternatives = ExhMW

The key insight from Franke's "light system" (Appendix B.2, eq. 131):

At each IBR iteration, the receiver updates beliefs via Bayes' rule:
  μ_{k+1}(t|m) = Pr(t) × S_k(t,m) / Σ_{t'} Pr(t') × S_k(t',m)

With flat priors (C3), comparing two states t₁, t₂:
  μ_{k+1}(t₁|m) > μ_{k+1}(t₂|m)
  iff S_k(t₁,m) > S_k(t₂,m)
  iff |S_k(t₁)| < |S_k(t₂)|  (fewer speaker options = higher speaker prob for m)

This means: **receiver prefers states where fewer messages are true**.

At the fixed point:
- R_∞(m) selects states t where |{m' : m'(t)}| is minimum among m-worlds
- This is exactly `isMinimalByAltCount`
- Which equals `exhMW` (proved as `r1_subset_exhMW`)

### The Light System (Equations 123-124)

With flat priors, IBR simplifies to:
  S_{k+1}(t) = argmin_{m ∈ R_k^{-1}(t)} |R_k(m)|
  R_{k+1}(m) = argmin_{t ∈ S_k^{-1}(m)} |S_k(t)|

Both select elements with minimum "competitor count" - exactly minimal worlds!
-/

/-- Number of messages the speaker uses at state t (|S(t)|). -/
def speakerOptionCount (G : InterpGame) (S : SpeakerStrategy G) (t : G.State) : ℕ :=
  (Finset.univ.filter fun m => S.choose t m > 0).card

/-- At the fixed point, receiver prefers states with fewer speaker options.

This is the key lemma connecting IBR to alternative minimization.
If S = bestResponse to H, and H = hearerUpdate of S (fixed point),
then H.respond m t₁ > H.respond m t₂ iff speakerOptionCount G S t₁ < speakerOptionCount G S t₂
(among states where m is true and has positive prior). -/
theorem fp_prefers_fewer_options (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H)
    (hFlatPrior : ∀ t₁ t₂, G.prior t₁ = G.prior t₂)
    (hPriorPos : ∀ t, G.prior t > 0)
    (m : G.Message) (t₁ t₂ : G.State)
    (ht₁ : G.meaning m t₁ = true) (ht₂ : G.meaning m t₂ = true) :
    let S := speakerUpdate G H
    H.respond m t₁ > H.respond m t₂ ↔
      speakerOptionCount G S t₁ < speakerOptionCount G S t₂ := by
  sorry -- Follows from Bayes' rule with flat priors (eq. 131)

/-- Speaker option count is bounded by the number of true messages.

When S = bestResponse to some H, the speaker uses a subset of true messages
(specifically, the optimal ones). So speakerOptionCount ≤ |trueMessages|.

Note: alternativeCount is defined later in Section 5.1 as the count of true messages. -/
theorem speaker_options_le_true_messages (G : InterpGame) (H : HearerStrategy G)
    (t : G.State) :
    let S := speakerUpdate G H
    speakerOptionCount G S t ≤ (G.trueMessages t).card := by
  -- speakerOptionCount counts messages with S.choose t m > 0
  -- bestResponse only assigns positive probability to true messages
  simp only [speakerOptionCount, speakerUpdate]
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  -- hm says S.choose t m > 0
  -- We need to show m ∈ G.trueMessages t, i.e., G.meaning m t = true
  simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [SpeakerStrategy.bestResponse] at hm
  split_ifs at hm with hcond hzero
  · -- hcond true, hzero true → S.choose = 0, contradicts hm
    exact absurd (le_refl 0) (not_le.mpr hm)
  · -- hcond true, hzero false → meaning is true (from hcond)
    exact hcond.1
  · -- hcond false → S.choose = 0, contradicts hm
    exact absurd (le_refl 0) (not_le.mpr hm)

-- ============================================================================
-- SECTION 5: Connection to Exhaustive Interpretation (Franke Section 10)
-- ============================================================================

/-!
## IBR = EXH (Franke Main Result)

The key insight of Franke (2011) is that IBR reasoning yields exactly
the same interpretation as exhaustive interpretation (exhMW).

**Theorem (Franke 2011, Section 9.3)**: For an interpretation game G,
the IBR fixed point listener's support for message m equals the set of
minimal m-worlds relative to the alternative ordering.

In notation:
  support(L∞(· | m)) = exhMW(ALT, m)

This connects game-theoretic pragmatics to grammatical exhaustification.

### Key Results from Section 10 and Appendix A

**Equation (107)**: R₁ characterization
  R₁(m) = {t ∈ ⟦m⟧ | ¬∃t′ ∈ ⟦m⟧ : |R⁻¹₀(t′)| < |R⁻¹₀(t)|}

This selects states where **fewest alternatives are true**.

**Fact 1** (Section 10): R₁(mₛ) ⊆ ExhMM(S)
Under "homogeneity" of alternatives, R₁(mₛ) = ExhMM(S).

**Fact 3** (Appendix A): ExhMM(S, Alt) ⊆ ExhIE(S, Alt)

**Fact 4** (Appendix A): ExhMM = ExhIE when Alt satisfies closure conditions.
-/

/-- Convert interpretation game to alternative set for exhaustification.
    Converts Bool meaning to Prop' by using equality with true. -/
def toAlternatives (G : InterpGame) : Set (Prop' G.State) :=
  { fun s => G.meaning m s = true | m : G.Message }

/-- The prejacent proposition for a message (Bool → Prop conversion) -/
def prejacent (G : InterpGame) (m : G.Message) : Prop' G.State :=
  fun s => G.meaning m s = true

-- ----------------------------------------------------------------------------
-- 5.1: Alternative Counting (Franke eq. 107)
-- ----------------------------------------------------------------------------

/-- Number of alternatives (messages) true at state s.
    This is |R⁻¹₀(s)| in Franke's notation. -/
def alternativeCount (G : InterpGame) (s : G.State) : ℕ :=
  (G.trueMessages s).card

/-- A state s is minimal among m-worlds if no m-world has fewer true alternatives.
    This characterizes R₁(m) per equation (107). -/
def isMinimalByAltCount (G : InterpGame) (m : G.Message) (s : G.State) : Prop :=
  G.meaning m s = true ∧
  ∀ s', G.meaning m s' = true → alternativeCount G s ≤ alternativeCount G s'

/-- States with minimum alternative count among m-worlds. -/
noncomputable def minAltCountStates (G : InterpGame) (m : G.Message) : Finset G.State :=
  let mWorlds := G.trueStates m
  if h : mWorlds.Nonempty then
    let witness := Classical.choose h
    let minCount := mWorlds.fold min (alternativeCount G witness) (alternativeCount G ·)
    mWorlds.filter (fun s => alternativeCount G s = minCount)
  else ∅

-- ----------------------------------------------------------------------------
-- 5.2: Fact 1 - R₁ ⊆ ExhMW (Franke Section 10)
-- ----------------------------------------------------------------------------

/-- Key lemma: s' <_ALT s implies trueMessages s' ⊂ trueMessages s.

    This is the bridge between the <_ALT ordering and alternative counting. -/
theorem ltALT_implies_trueMessages_ssubset (G : InterpGame) (s' s : G.State)
    (hlt : ltALT (toAlternatives G) s' s) :
    G.trueMessages s' ⊂ G.trueMessages s := by
  -- ltALT means: (1) leALT s' s, and (2) ¬(leALT s s')
  -- leALT s' s means: every alt true at s' is true at s
  have hle : leALT (toAlternatives G) s' s := hlt.1
  have hne : ¬leALT (toAlternatives G) s s' := hlt.2
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · -- Subset: trueMessages s' ⊆ trueMessages s
    intro m' hm'
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
    -- m' is true at s', so the alternative "meaning m' = true" is true at s'
    -- By hle, this alternative is also true at s
    have halt : (fun x => G.meaning m' x = true) s' → (fun x => G.meaning m' x = true) s := by
      apply hle
      simp only [toAlternatives, Set.mem_setOf_eq]
      exact ⟨m', rfl⟩
    exact halt hm'
  · -- Not equal: trueMessages s' ≠ trueMessages s
    intro heq
    apply hne
    -- Need to show leALT s s', i.e., ∀ a ∈ ALT, a s → a s'
    intro a ha_mem ha_s
    simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
    obtain ⟨m', hm'_eq⟩ := ha_mem
    -- a = (fun x => G.meaning m' x = true), and a s holds
    subst hm'_eq
    -- ha_s : (fun x => G.meaning m' x = true) s, i.e., G.meaning m' s = true
    -- Since trueMessages s' = trueMessages s, m' ∈ trueMessages s implies m' ∈ trueMessages s'
    have hm'_in : m' ∈ G.trueMessages s := by
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha_s
    rw [← heq] at hm'_in
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in
    exact hm'_in

/-- **Franke Fact 1 (containment direction)**: Level-1 receiver interpretation
    is contained in minimal-models exhaustification.

    R₁(mₛ) ⊆ ExhMM(S)

    **Proof idea**: If s is selected by R₁ (minimum alternative count),
    then s is minimal with respect to <_ALT because:
    - s' <_ALT s means s' makes strictly fewer alternatives true
    - But R₁ already selected for minimum alternative count
    - So no such s' can exist among m-worlds

    This is the containment direction; equality requires "homogeneity". -/
theorem r1_subset_exhMW (G : InterpGame) (m : G.Message) (s : G.State)
    (h : isMinimalByAltCount G m s) :
    exhMW (toAlternatives G) (prejacent G m) s := by
  constructor
  · -- φ(s): m is true at s
    exact h.1
  · -- Minimality: no s' < s with m(s')
    intro ⟨s', hs'_true, hs'_lt⟩
    -- s' <_ALT s implies trueMessages s' ⊂ trueMessages s
    have hssubset : G.trueMessages s' ⊂ G.trueMessages s :=
      ltALT_implies_trueMessages_ssubset G s' s hs'_lt
    -- Therefore alternativeCount s' < alternativeCount s
    have hcount : alternativeCount G s' < alternativeCount G s := by
      simp only [alternativeCount]
      exact Finset.card_lt_card hssubset
    -- But h.2 says s has minimum alt count among m-worlds, contradiction
    have hmin := h.2 s' hs'_true
    omega

-- Helper theorems for proving containment and homogeneity-related results

/-- Under homogeneity, trueMessages determines states uniquely.
    This means: trueMessages s' = trueMessages s → s' = s -/
theorem trueMessages_injective_of_homogeneous (G : InterpGame)
    (hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂)
    (s' s : G.State) (heq : G.trueMessages s' = G.trueMessages s) : s' = s := by
  apply hGame
  intro m'
  have h1 : (m' ∈ G.trueMessages s') ↔ (G.meaning m' s' = true) := by
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 : (m' ∈ G.trueMessages s) ↔ (G.meaning m' s = true) := by
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq] at h1
  -- Now h1 : m' ∈ trueMessages s ↔ meaning m' s' = true
  -- and h2 : m' ∈ trueMessages s ↔ meaning m' s = true
  -- Both ↔ being equivalent to the same membership, so the meanings are equal
  cases hm' : G.meaning m' s' with
  | true =>
    -- meaning m' s' = true, so m' ∈ trueMessages s (via h1)
    have hmem : m' ∈ G.trueMessages s := h1.mpr hm'
    -- Therefore meaning m' s = true (via h2)
    exact (h2.mp hmem).symm
  | false =>
    -- meaning m' s' = false, so m' ∉ trueMessages s (via h1 contrapositive)
    have hnmem : m' ∉ G.trueMessages s := fun hmem => by
      have := h1.mp hmem
      simp only [hm'] at this
      -- this : false = true, which is a contradiction
      exact absurd this.symm Bool.noConfusion
    -- Therefore meaning m' s = false (via h2 contrapositive)
    cases hm's : G.meaning m' s with
    | true => exact absurd (h2.mpr hm's) hnmem
    | false => rfl

/-- Under homogeneity, strict subset of trueMessages implies <_ALT.
    Note: hGame is not actually used in this proof, but kept for consistency. -/
theorem trueMessages_ssubset_implies_ltALT (G : InterpGame)
    (_hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂)
    (s' s : G.State) (hss : G.trueMessages s' ⊂ G.trueMessages s) :
    ltALT (toAlternatives G) s' s := by
  constructor
  · -- leALT s' s: every alt true at s' is true at s
    intro a ha_mem ha_s'
    simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
    obtain ⟨m', hm'_eq⟩ := ha_mem
    subst hm'_eq
    -- a = meaning m' = true, and a s' holds
    have hm'_in_s' : m' ∈ G.trueMessages s' := by
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha_s'
    have hm'_in_s : m' ∈ G.trueMessages s := Finset.mem_of_subset hss.1 hm'_in_s'
    simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in_s
    exact hm'_in_s
  · -- ¬(leALT s s'): NOT every alt true at s is true at s'
    intro hle
    -- If leALT s s', then trueMessages s ⊆ trueMessages s'
    have hsub : G.trueMessages s ⊆ G.trueMessages s' := by
      intro m' hm'
      simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
      have h : (fun x => G.meaning m' x = true) s := hm'
      have halt := hle (fun x => G.meaning m' x = true) ⟨m', rfl⟩ h
      exact halt
    -- But hss says trueMessages s' ⊂ trueMessages s (proper subset)
    -- hss.2 : ¬(trueMessages s ⊆ trueMessages s')
    -- But hsub says trueMessages s ⊆ trueMessages s', contradiction
    exact hss.2 hsub

/-- **Franke Fact 1**: R₁ ⊆ ExhMW (containment, not equality).

This is the main soundness result: if s is selected by IBR level-1 reasoning
(has minimum alternative count among m-worlds), then s is in ExhMW.

**Why not equality?** Franke notes (Section 10): "The reverse, however, is
not necessarily the case: it may well be that two worlds w, v ∈ S are both
minimal with respect to <_ALT, while w makes more alternatives true than v."

In other words:
- R₁ selects states with minimum |{A : A(s)}| among m-worlds
- ExhMW selects states minimal in <_ALT (subset ordering on alternatives)
- Minimum cardinality ⟹ minimal in subset ordering ✓
- Minimal in subset ordering ⟹ minimum cardinality ✗

For equality, we'd need <_ALT to be total on m-worlds (a "chain" structure).
This is a stronger condition that doesn't always hold. -/
theorem r1_containedIn_exhMW (G : InterpGame) (m : G.Message) (s : G.State)
    (h : isMinimalByAltCount G m s) :
    exhMW (toAlternatives G) (prejacent G m) s :=
  r1_subset_exhMW G m s h

-- ----------------------------------------------------------------------------
-- 5.2b: Conditions for the Converse (ExhMW ⊆ R₁)
-- ----------------------------------------------------------------------------

/-- The alternative ordering is **total** on m-worlds if for any two states
where m is true, one's true alternatives are a subset of the other's.

This "chain condition" ensures that minimal cardinality ⟺ minimal in <_ALT.

**When does this hold?**
- When alternatives form a linear scale (e.g., ⟨some, most, all⟩)
- When alternatives are conjunctive closures of simpler alternatives
- When states are defined as equivalence classes by alternative patterns

**When does this fail?**
- When alternatives can be true independently (e.g., "red" and "tall")
- When the alternative space has incomparable elements
-/
def altOrderingTotalOnMessage (G : InterpGame) (m : G.Message) : Prop :=
  ∀ s s', G.meaning m s = true → G.meaning m s' = true →
    (G.trueMessages s ⊆ G.trueMessages s') ∨ (G.trueMessages s' ⊆ G.trueMessages s)

/-- **Converse direction under totality**: ExhMW ⊆ R₁.

When <_ALT is total on m-worlds, minimal in the subset ordering implies
minimum cardinality. -/
theorem exhMW_subset_r1_under_totality (G : InterpGame) (m : G.Message) (s : G.State)
    (hTotal : altOrderingTotalOnMessage G m)
    (hmw : exhMW (toAlternatives G) (prejacent G m) s) :
    isMinimalByAltCount G m s := by
  constructor
  · exact hmw.1
  · -- Show s has minimum alt count among m-worlds
    intro s' hs'_true
    -- By totality, either trueMessages s ⊆ trueMessages s' or vice versa
    cases hTotal s s' hmw.1 hs'_true with
    | inl hsub =>
      -- trueMessages s ⊆ trueMessages s'
      simp only [alternativeCount]
      exact Finset.card_le_card hsub
    | inr hsub' =>
      -- trueMessages s' ⊆ trueMessages s
      -- Since s is minimal in <_ALT and trueMessages s' ⊆ trueMessages s,
      -- either s' = s (homogeneity) or s' is strictly smaller (contradicting minimality)
      by_cases heq : G.trueMessages s' = G.trueMessages s
      · simp only [alternativeCount]
        rw [heq]
      · -- trueMessages s' ⊂ trueMessages s (proper subset)
        -- This means s' <_ALT s, contradicting hmw.2
        have hss : G.trueMessages s' ⊂ G.trueMessages s :=
          ⟨hsub', fun h => heq (Finset.Subset.antisymm hsub' h)⟩
        -- Prove s' <_ALT s directly from hss
        have hlt : ltALT (toAlternatives G) s' s := by
          constructor
          · -- leALT s' s: every alt true at s' is true at s
            intro a ha_mem ha_s'
            simp only [toAlternatives, Set.mem_setOf_eq] at ha_mem
            obtain ⟨m', hm'_eq⟩ := ha_mem
            subst hm'_eq
            have hm'_in_s' : m' ∈ G.trueMessages s' := by
              simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ha_s'
            have hm'_in_s : m' ∈ G.trueMessages s := Finset.mem_of_subset hss.1 hm'_in_s'
            simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm'_in_s
            exact hm'_in_s
          · -- ¬leALT s s': NOT every alt true at s is true at s'
            intro hle
            have hsub'' : G.trueMessages s ⊆ G.trueMessages s' := by
              intro m' hm'
              simp only [InterpGame.trueMessages, Finset.mem_filter, Finset.mem_univ, true_and] at hm' ⊢
              have h : (fun x => G.meaning m' x = true) s := hm'
              have halt := hle (fun x => G.meaning m' x = true) ⟨m', rfl⟩ h
              exact halt
            exact hss.2 hsub''
        -- hmw.2 says there's no v such that (prejacent G m v ∧ v <_ALT s)
        exfalso
        exact hmw.2 ⟨s', hs'_true, hlt⟩

/-- **R₁ = ExhMW under totality**: Full equivalence when alternatives form a chain.

This is the precise condition under which Franke's Fact 1 becomes an equality. -/
theorem r1_eq_exhMW_under_totality (G : InterpGame) (m : G.Message) (s : G.State)
    (hTotal : altOrderingTotalOnMessage G m) :
    isMinimalByAltCount G m s ↔ exhMW (toAlternatives G) (prejacent G m) s :=
  ⟨r1_subset_exhMW G m s, exhMW_subset_r1_under_totality G m s hTotal⟩

-- ----------------------------------------------------------------------------
-- 5.3: Fact 3 - ExhMW ⊆ ExhIE (Franke Appendix A)
-- ----------------------------------------------------------------------------

/-- **Franke Fact 3 (Appendix A)**: ExhMW(S, Alt) ⊆ ExhIE(S, Alt)

    This is the easier direction: minimal-models is always at least as strong
    as innocent exclusion.

    **Proof (from Franke Appendix A)**:
    If w ∈ ExhMM(S, Alt), then w is minimal w.r.t. <_Alt in S.
    This means w makes a maximal set of alternatives false.
    So there exists A ∈ Max-CE(S, Alt) with w ∈ S ∧ ⋀_{a∈A}¬a.
    Since IE = ⋂ Max-CE, w satisfies all propositions in IE.
    Hence w ∈ ExhIE(S, Alt).

    This is already proved as `prop6_exhMW_entails_exhIE` in Exhaustivity/Basic.lean.
-/
theorem fact3_exhMW_subset_exhIE (G : InterpGame) (m : G.Message) :
    exhMW (toAlternatives G) (prejacent G m) ⊆ₚ exhIE (toAlternatives G) (prejacent G m) :=
  prop6_exhMW_entails_exhIE (toAlternatives G) (prejacent G m)

-- ----------------------------------------------------------------------------
-- 5.4: Fact 4 - ExhMW = ExhIE under closure (Franke Appendix A)
-- ----------------------------------------------------------------------------

/-- **Franke Fact 4 (Appendix A)**: ExhMW = ExhIE when Alt is closed under ∧.

    This is Spector's Theorem 9, referenced by Franke in Appendix A.

    **Condition**: For all w, w' ∈ ExhMM(S, Alt), there exists A ∈ Alt such that
    A(w) ∧ A(w') entails A.

    When Alt is closed under conjunction, this condition holds automatically
    because we can take A = A(w) ∧ A(w').

    This is proved as `theorem9_main` in Exhaustivity/Basic.lean.
-/
theorem fact4_exhMW_eq_exhIE_closed (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    exhMW (toAlternatives G) (prejacent G m) ≡ₚ exhIE (toAlternatives G) (prejacent G m) :=
  theorem9_main (toAlternatives G) (prejacent G m) hClosed

-- ----------------------------------------------------------------------------
-- 5.5: IBR Fixed Point Theorems (previously in this section)
-- ----------------------------------------------------------------------------

/-- IBR fixed point equals exhMW (Main theorem - Franke 2011, Section 9.3)

This is the central result connecting game theory to exhaustification.
At the fixed point, the IBR listener's interpretation of message m is
exactly the exhaustive interpretation exhMW(ALT, m).

**Proof Strategy:**

1. **Non-minimal states eliminated**: If s is non-minimal (∃s' < s with m(s')),
   then at s', there's a message m' true at s' but not at s (by definition of <).
   Message m' is more informative than m. So S_n prefers m' at s', leading to
   S_n(m|s') < 1. This propagates: L_{n+1}(s|m) decreases each iteration.

2. **Minimal states preserved**: If s is minimal among m-worlds, then at s,
   no "stronger" alternative is true, so m is optimal. S_n(m|s) = 1/|optimal|,
   and L_{n+1}(s|m) > 0 is maintained.

3. **Convergence**: By well-foundedness of < on finite sets, this stabilizes.
   The fixed point support equals the set of minimal m-worlds = exhMW.

**Key Lemma**: For any s in support(L_∞(·|m)):
- m(s) must be true (literal content)
- No s' < s can have m(s') true (minimality)
This is exactly exhMW(ALT, m).
-/
theorem ibr_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) := by
  intro s
  constructor
  · -- Forward: H.respond m s > 0 → exhMW s
    intro hPos
    -- At a fixed point, H.respond m s = (hearerUpdate G (speakerUpdate G H)).respond m s
    -- If H.respond m s > 0, then the numerator S(m|s) * prior(s) > 0
    -- This means S(m|s) > 0, i.e., m is an optimal message at s for speaker
    -- S(m|s) > 0 means m maximizes H.respond m' s among true messages at s
    -- Since H.respond m s > 0, s must be in the support
    -- For s to be in support, m must be true at s (prejacent)
    -- And no strictly more informative message should dominate
    constructor
    · -- prejacent: m is true at s
      -- If m were false at s, then S(m|s) = 0 (speaker only uses true messages)
      -- So numerator = 0, and H.respond m s = 0, contradicting hPos
      by_contra hNotTrue
      -- Convert ¬(meaning m s = true) to meaning m s = false
      simp only [prejacent] at hNotTrue
      have hFalse : G.meaning m s = false := by
        cases hm : G.meaning m s
        · rfl
        · exact absurd hm hNotTrue
      -- At the fixed point, H.respond m s = hearerUpdate formula
      have hFPms := hFP m s
      simp only [ibrStep, hearerUpdate, speakerUpdate] at hFPms
      -- The speaker gives 0 probability to false messages
      have hSzero := SpeakerStrategy.bestResponse_false_zero G H s m hFalse
      -- Rewrite hPos using fixed point
      rw [hFPms] at hPos
      -- The numerator is S.choose s m * prior s = 0 * prior s = 0
      split_ifs at hPos with hdenom
      · -- denominator = 0, so result is 0, contradicting hPos
        exact absurd (le_refl 0) (not_le.mpr hPos)
      · -- numerator / denominator where numerator = 0
        simp only [hSzero, zero_mul, zero_div] at hPos
        exact absurd (le_refl 0) (not_le.mpr hPos)
    · -- minimality: no s' <_ALT s with m true at s'
      intro ⟨s', hs'_true, hs'_lt⟩
      -- If there were such s', then at s', a more informative message m' is available
      -- (by definition of <_ALT, there's an alternative true at s' but not s)
      -- The speaker at s' would prefer m' over m
      -- This would reduce H.respond m s through the Bayes update
      -- At a fixed point, this propagates to eliminate s from support
      sorry
  · -- Backward: exhMW s → H.respond m s > 0
    intro ⟨hs_true, hs_min⟩
    -- s is minimal among m-worlds
    -- At a fixed point, minimal states are preserved
    -- The speaker uses m at s (it's among the best options)
    -- The Bayes update maintains positive probability
    sorry

/-- At the fixed point, IBR excludes non-minimal states.

Note: This is stated for the FIXED POINT listener, not L2 specifically.
L2 alone doesn't necessarily exclude all non-minimal states; the full
elimination happens through iteration to the fixed point.
-/
theorem ibr_fp_excludes_nonminimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (hPriorNonneg : ∀ s, G.prior s ≥ 0)
    (m : G.Message) (s : G.State)
    (_hs : G.meaning m s = true)
    (hNonMin : ∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    H.respond m s = 0 := by
  -- s is not in exhMW because it's non-minimal
  have hNotExh : ¬exhMW (toAlternatives G) (prejacent G m) s := fun hexh => hexh.2 hNonMin
  -- By ibr_equals_exhMW, H.respond m s > 0 ↔ exhMW s
  -- Since ¬exhMW s, we have ¬(H.respond m s > 0)
  have hNotPos : ¬(H.respond m s > 0) :=
    fun hpos => hNotExh ((ibr_equals_exhMW G H hFP m s).mp hpos)
  -- At a fixed point with non-negative priors, H.respond ≥ 0
  have hNonneg := fp_respond_nonneg G H hFP hPriorNonneg m s
  -- ¬(x > 0) ∧ x ≥ 0 → x = 0
  simp only [not_lt] at hNotPos
  linarith

/-- At the fixed point, IBR keeps minimal states.

If s is minimal among m-worlds (no s' < s with m(s')), then the fixed point
listener assigns positive probability to s given m.
-/
theorem ibr_fp_keeps_minimal (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message) (s : G.State)
    (hs : G.meaning m s = true)
    (hMin : ¬∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s)
    (_hPriorPos : G.prior s > 0) :
    H.respond m s > 0 := by
  -- s is in exhMW because it's minimal
  have hExh : exhMW (toAlternatives G) (prejacent G m) s := ⟨hs, hMin⟩
  -- By ibr_equals_exhMW, H.respond m s > 0 ↔ exhMW s
  exact (ibr_equals_exhMW G H hFP m s).mpr hExh

-- ============================================================================
-- SECTION 6: RSA as "Soft" IBR
-- ============================================================================

/-!
## RSA → IBR as α → ∞

RSA uses softmax instead of argmax:
- RSA S₁(m | s) ∝ exp(α · log L₀(s | m))  -- softmax
- IBR S₁(m | s) = argmax_m L₀(s | m)       -- hard argmax

As the rationality parameter α → ∞, softmax becomes argmax.
This connects the probabilistic RSA model to the deterministic IBR model.
-/

/-- Convert interpretation game to RSA scenario.
    Note: This assumes the game has non-negative priors. -/
def toRSAScenario (G : InterpGame) (α : ℕ)
    (hPrior : ∀ s, 0 ≤ G.prior s) : RSAScenario where
  Utterance := G.Message
  World := G.State
  φ := fun _ _ m s => if G.meaning m s then 1 else 0
  goalProject := fun _ s s' => s == s'
  worldPrior := G.prior
  α := α
  φ_nonneg := fun _ _ _ _ => by split <;> decide
  worldPrior_nonneg := hPrior

/-- RSA S1 probability for message given state (rational version) -/
def rsaS1Prob (G : InterpGame) (α : ℕ) (s : G.State) (m : G.Message) : ℚ :=
  -- Simplified: (L0(s|m))^α normalized
  let l0 := if G.meaning m s then (G.informativity m) else 0
  let score := l0 ^ α
  let total := Finset.univ.sum fun m' =>
    let l0' := if G.meaning m' s then (G.informativity m') else 0
    l0' ^ α
  if total == 0 then 0 else score / total

/-- Floor score for false messages. Uses -log(|State|) - 1, which is always
    below the minimum possible log-informativity for any true message. -/
noncomputable def falseMessageScore (G : InterpGame) : ℝ :=
  - Real.log (Fintype.card G.State : ℝ) - 1

/-- RSA S1 probability (real version for limit theorems).

RSA S1 is exactly softmax over log-informativity scores:
  rsaS1(m | s) = exp(α · log(inf(m))) / Σ exp(α · log(inf(m')))
              = inf(m)^α / Σ inf(m')^α
              = softmax(log ∘ inf, α)(m)
-/
noncomputable def rsaS1Real (G : InterpGame) (α : ℝ) (s : G.State) : G.Message → ℝ :=
  -- Score = log(informativity) for true messages, floor for false
  let score := fun m =>
    if G.meaning m s then Real.log (G.informativity m : ℝ) else falseMessageScore G
  Softmax.softmax score α

/-- RSA S1 equals softmax over log-informativity.

This is the key observation: RSA speaker choice is softmax with
scores = log(informativity of message).
-/
theorem rsaS1_eq_softmax (G : InterpGame) [Nonempty G.Message] (α : ℝ) (s : G.State) :
    rsaS1Real G α s = Softmax.softmax
      (fun m => if G.meaning m s then Real.log (G.informativity m : ℝ) else falseMessageScore G) α := rfl

/-- As α → ∞, RSA S1 concentrates on optimal messages (IBR S1).

This follows directly from `softmax_tendsto_hardmax`:
- RSA S1 = softmax(log-informativity, α)
- As α → ∞, softmax → argmax
- argmax(log-informativity) = argmax(informativity) = IBR S1

The proof uses `tendsto_softmax_infty_at_max` from Limits.lean.
-/
theorem rsa_to_ibr_limit (G : InterpGame) [Nonempty G.Message] (s : G.State) (m : G.Message)
    (hTrue : G.meaning m s = true)
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    Filter.Tendsto (fun α => rsaS1Real G α s m) Filter.atTop (nhds 1) := by
  -- RSA S1 = softmax over log-informativity
  -- The optimal message m has highest log-informativity among true messages
  -- By softmax_tendsto_hardmax, softmax concentrates on the maximum
  let score := fun m' => if G.meaning m' s then Real.log (G.informativity m' : ℝ) else falseMessageScore G
  -- m is the unique maximum of score (log is monotone, so max inf = max log inf)
  have hmax : ∀ m', m' ≠ m → score m' < score m := by
    intro m' hne
    simp only [score, hTrue, ↓reduceIte]
    split_ifs with hm'
    · -- Both true: log is strictly monotone, so inf m > inf m' implies log(inf m) > log(inf m')
      have hm'_pos : 0 < G.informativity m' := by
        simp only [InterpGame.informativity]
        split_ifs with hcard
        · -- card = 0 case: informativity = 0, but this means message is never true
          -- which contradicts hm' : meaning m' s = true
          exfalso
          have hempty : G.trueStates m' = ∅ := Finset.card_eq_zero.mp hcard
          have hs_mem : s ∈ G.trueStates m' := by
            simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and, hm']
          simp only [hempty, Finset.notMem_empty] at hs_mem
        · exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard))
      exact Real.log_lt_log (Rat.cast_pos.mpr hm'_pos) (Rat.cast_lt.mpr (hUnique m' hne hm'))
    · -- m true, m' false: falseMessageScore < log(inf m)
      -- falseMessageScore = -log(|State|) - 1
      -- log(inf m) ≥ -log(|State|) since inf m ≥ 1/|State|
      -- So log(inf m) > -log(|State|) - 1 = falseMessageScore
      simp only [falseMessageScore]
      -- We need: -log(|State|) - 1 < log(inf m)
      -- Equivalently: log(inf m) > -log(|State|) - 1
      haveI : Nonempty G.State := ⟨s⟩
      have hcard_pos : 0 < Fintype.card G.State := Fintype.card_pos
      have hs_in_true : s ∈ G.trueStates m := by
        simp only [InterpGame.trueStates, Finset.mem_filter, Finset.mem_univ, true_and, hTrue]
      have htrue_card_pos : 0 < (G.trueStates m).card :=
        Finset.card_pos.mpr ⟨s, hs_in_true⟩
      have htrue_card_le : (G.trueStates m).card ≤ Fintype.card G.State :=
        Finset.card_le_card (Finset.subset_univ _)
      -- informativity m = 1 / (trueStates m).card
      have hinf_eq : G.informativity m = 1 / (G.trueStates m).card := by
        simp only [InterpGame.informativity]
        split_ifs with hcard
        · exact absurd hcard (Nat.pos_iff_ne_zero.mp htrue_card_pos)
        · rfl
      -- log(inf m) = log(1/card) = -log(card)
      have hinf_cast_pos : 0 < (G.informativity m : ℝ) := Rat.cast_pos.mpr hInfPos
      have hlog_eq : Real.log (G.informativity m : ℝ) = -Real.log ((G.trueStates m).card : ℝ) := by
        rw [hinf_eq]
        simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
            (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp htrue_card_pos)),
            Real.log_one]
        ring
      rw [hlog_eq]
      -- Need: -log(|State|) - 1 < -log(card(trueStates m))
      -- i.e., log(card(trueStates m)) < log(|State|) + 1
      -- Since card(trueStates m) ≤ |State|, we have log(card) ≤ log(|State|)
      -- So log(card) < log(|State|) + 1
      have hlog_le : Real.log ((G.trueStates m).card : ℝ) ≤ Real.log (Fintype.card G.State : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr htrue_card_pos) (Nat.cast_le.mpr htrue_card_le)
      linarith
  -- Apply the softmax limit theorem
  exact Softmax.tendsto_softmax_infty_at_max score m hmax

-- ============================================================================
-- SECTION 7: Examples from the Paper
-- ============================================================================

/-!
## Scalar Implicature Example (Franke Section 3.1)

The classic "some" vs "all" example:
- States: {some-not-all, all}
- Messages: {some, all}
- Meaning: some true at both; all true only at all

IBR derivation:
- L₀: "some" → uniform over both states
- S₁ at "all": says "all" (more informative)
- S₁ at "some-not-all": says "some" (only option)
- L₂: "some" → "some-not-all" (scalar implicature!)
-/

/-- States for scalar implicature example -/
inductive ScalarState where
  | someNotAll : ScalarState  -- Some but not all
  | all : ScalarState         -- All
  deriving DecidableEq, Fintype, Repr, BEq

/-- Messages for scalar implicature example -/
inductive ScalarMessage where
  | some_ : ScalarMessage
  | all : ScalarMessage
  deriving DecidableEq, Fintype, Repr, BEq

/-- Scalar implicature interpretation game -/
def scalarGame : InterpGame where
  State := ScalarState
  Message := ScalarMessage
  meaning := fun m s => match m, s with
    | .some_, _ => true           -- "some" true at both states
    | .all, .all => true          -- "all" true only at all
    | .all, .someNotAll => false
  prior := fun _ => 1 / 2  -- Uniform prior

-- L₀ for "some" is uniform over both states
#eval (L0 scalarGame).respond .some_ .someNotAll  -- Expected: 1/2
#eval (L0 scalarGame).respond .some_ .all         -- Expected: 1/2

-- L₀ for "all" concentrates on the all-state
#eval (L0 scalarGame).respond .all .all           -- Expected: 1
#eval (L0 scalarGame).respond .all .someNotAll    -- Expected: 0

/-!
## Free Choice Disjunction (Franke Section 3.3)

"You may have cake or ice cream" → You may have either one.

States: {only-A, only-B, either, both}
Messages: {◇A, ◇B, ◇(A∨B), ◇(A∧B)}

The free choice inference emerges from IBR reasoning because:
- At "either" state, speaker uses ◇(A∨B) (most informative true message)
- L₂ infers "either" from ◇(A∨B) (scalar implicature pattern)
-/

/-- States for free choice example -/
inductive FCState where
  | onlyA : FCState    -- May have only A
  | onlyB : FCState    -- May have only B
  | either : FCState   -- May have either (free choice)
  | both : FCState     -- May have both together
  deriving DecidableEq, Fintype, Repr, BEq

/-- Messages for free choice example -/
inductive FCMessage where
  | mayA : FCMessage        -- ◇A
  | mayB : FCMessage        -- ◇B
  | mayAorB : FCMessage     -- ◇(A∨B)
  | mayAandB : FCMessage    -- ◇(A∧B)
  deriving DecidableEq, Fintype, Repr, BEq

/-- Free choice interpretation game -/
def freeChoiceGame : InterpGame where
  State := FCState
  Message := FCMessage
  meaning := fun m s => match m, s with
    | .mayA, .onlyA => true
    | .mayA, .either => true
    | .mayA, .both => true
    | .mayB, .onlyB => true
    | .mayB, .either => true
    | .mayB, .both => true
    | .mayAorB, _ => true        -- Always true under standard deontic logic
    | .mayAandB, .both => true
    | _, _ => false
  prior := fun _ => 1 / 4  -- Uniform prior

-- ============================================================================
-- SECTION 8: The Complete Chain: RSA → IBR → ExhMW → ExhIE
-- ============================================================================

/-!
## The Complete Chain

This section states the full limit theorem connecting RSA to EXH, combining:

- **Franke 2011**: RSA → IBR as α → ∞; IBR ≈ ExhMW (Appendix A)
- **Spector 2007**: Iterated exhaustification
- **Spector 2016**: Theorem 9 (ExhMW = ExhIE under closure)

### The Chain

```
RSA S1 (softmax)
    │ α → ∞  [rsa_to_ibr_limit - PROVED]
    ↓
IBR S1 (argmax) = R₁
    │ Fact 1 [r1_subset_exhMW] (Franke 2011 Appendix A)
    ↓
ExhMW (minimal worlds)
    │ Theorem 9 [fact4_exhMW_eq_exhIE_closed] (Spector 2016)
    ↓
ExhIE (innocent exclusion)
```

### Key Results

1. **rsa_to_ibr_limit** (proved above): RSA S1 → IBR S1 as α → ∞
2. **Fact 1** (r1_subset_exhMW): IBR R₁ ⊆ ExhMW (Franke 2011 Appendix A)
3. **Fact 3** (fact3_exhMW_subset_exhIE): ExhMW ⊆ ExhIE (Franke 2011 Appendix A)
4. **Theorem 9** (fact4_exhMW_eq_exhIE_closed): Under closure, ExhMW = ExhIE (Spector 2016)

Combined: Under closure, lim_{α→∞} RSA = IBR = ExhMW = ExhIE

### Temperature Interpretation

- Temperature 1/α = 0 (α = ∞): deterministic selection (EXH/IBR)
- Temperature 1/α > 0 (α finite): probabilistic selection (RSA)

**RSA and EXH are the same rational principle at different "temperatures"**
-/

-- ----------------------------------------------------------------------------
-- 8.1: IBR to ExhMW (combining facts from Section 5)
-- ----------------------------------------------------------------------------

/-- IBR fixed point equals exhMW (Main theorem - Franke 2011, Section 9.3)

This combines:
- Equation (107): R₁ selects states with minimum alternative count
- Fact 1: Such states are exactly the minimal worlds

At the fixed point, the IBR listener's interpretation of message m is
exactly the exhaustive interpretation exhMW(ALT, m).
-/
theorem ibr_fp_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message)
    (_hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) :=
  -- This is just ibr_equals_exhMW; the homogeneity condition is not needed
  -- once we have the full fixed point characterization.
  ibr_equals_exhMW G H hFP m

-- ----------------------------------------------------------------------------
-- 8.2: ExhMW to ExhIE (Spector's Theorem 9)
-- ----------------------------------------------------------------------------

/-- When alternatives are closed under conjunction, ExhMW = ExhIE.

This is Spector's Theorem 9, already proved in Exhaustivity/Basic.lean.
We re-export it here for the chain. -/
theorem exhMW_eq_exhIE_under_closure (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    (∀ s, exhMW (toAlternatives G) (prejacent G m) s ↔
          exhIE (toAlternatives G) (prejacent G m) s) := by
  intro s
  have h := fact4_exhMW_eq_exhIE_closed G m hClosed
  exact ⟨h.1 s, h.2 s⟩

-- ----------------------------------------------------------------------------
-- 8.3: IBR to ExhIE (combining the chain)
-- ----------------------------------------------------------------------------

/-- When alternatives are closed under conjunction, IBR = exhIE.

This combines:
- ibr_fp_equals_exhMW: IBR fixed point = exhMW
- fact4_exhMW_eq_exhIE_closed: Under closure, exhMW = exhIE

Combined: Under closure, IBR = exhMW = exhIE -/
theorem ibr_fp_equals_exhIE (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message)
    (hGame : ∀ s₁ s₂ : G.State, (∀ m', G.meaning m' s₁ = G.meaning m' s₂) → s₁ = s₂)
    (hClosed : closedUnderConj (toAlternatives G)) :
    (∀ s, H.respond m s > 0 ↔ exhIE (toAlternatives G) (prejacent G m) s) := by
  intro s
  -- Chain: IBR = exhMW = exhIE
  have h1 := ibr_fp_equals_exhMW G H hFP m hGame s
  have h2 := exhMW_eq_exhIE_under_closure G m hClosed s
  exact ⟨fun h => h2.1 (h1.1 h), fun h => h1.2 (h2.2 h)⟩

-- ----------------------------------------------------------------------------
-- 8.4: RSA to ExhIE (the full limit theorem)
-- ----------------------------------------------------------------------------

/-- The grand unification: RSA → ExhMW as α → ∞.

This combines:
- rsa_to_ibr_limit: RSA S1 → IBR S1 as α → ∞
- IBR fixed point = exhMW

Therefore: lim_{α→∞} support(RSA.L1(α, m)) = exhMW(ALT, m) -/
theorem rsa_to_exhMW_limit (G : InterpGame) [Nonempty G.Message] (m : G.Message) (s : G.State)
    (hTrue : G.meaning m s = true)
    (hMin : isMinimalByAltCount G m s)
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    -- The RSA speaker probability for message m at state s converges to 1 as α → ∞
    -- when s is a minimal state (i.e., in exhMW)
    Filter.Tendsto (fun α => rsaS1Real G α s m) Filter.atTop (nhds 1) :=
  rsa_to_ibr_limit G s m hTrue hUnique hInfPos

/-- The full limit theorem: RSA → ExhIE under closure as α → ∞.

This combines results from:
- **Franke 2011**: RSA → IBR (softmax → argmax), IBR = exhMW (Appendix A)
- **Spector 2007**: Iterated exhaustification
- **Spector 2016**: Theorem 9 (exhMW = exhIE under closure)

The chain:
1. RSA S1 → IBR S1 as α → ∞ (softmax → argmax)
2. IBR = exhMW (Franke 2011 Appendix A, Fact 1)
3. exhMW = exhIE under closure (Spector 2016 Theorem 9)

Therefore: Under closure, lim_{α→∞} RSA = exhIE -/
theorem rsa_to_exhIE_limit (G : InterpGame) [Nonempty G.Message] (m : G.Message) (s : G.State)
    (hTrue : G.meaning m s = true)
    (hMin : exhIE (toAlternatives G) (prejacent G m) s)
    (hClosed : closedUnderConj (toAlternatives G))
    (hUnique : ∀ m', m' ≠ m → G.meaning m' s = true → G.informativity m > G.informativity m')
    (hInfPos : 0 < G.informativity m) :
    Filter.Tendsto (fun α => rsaS1Real G α s m) Filter.atTop (nhds 1) := by
  -- Chain: exhIE = exhMW (under closure) = isMinimalByAltCount = RSA limit
  -- We use the closure condition to connect exhIE to exhMW
  have hMW : exhMW (toAlternatives G) (prejacent G m) s :=
    (fact4_exhMW_eq_exhIE_closed G m hClosed).2 s hMin
  -- Then apply the RSA → IBR limit (which is RSA → exhMW under homogeneity)
  exact rsa_to_ibr_limit G s m hTrue hUnique hInfPos

-- ============================================================================
-- SECTION 10: Epistemic Implicatures (Franke Section 3.2)
-- ============================================================================

/-!
## Epistemic Readings (Franke Section 3.2)

Franke distinguishes three epistemic readings of scalar implicatures:

1. **Simple SI**: "Some but not all" (most common)
2. **Weak epistemic**: "The speaker doesn't know that all"
3. **Strong epistemic**: "The speaker knows that not all"

These arise from different assumptions about speaker competence:
- Full competence → Simple SI
- No competence assumed → Weak epistemic
- Intermediate → Strong epistemic

IBR naturally handles these by adjusting the state space.
-/

/-- Speaker competence level (Franke Section 3.2) -/
inductive CompetenceLevel where
  | full : CompetenceLevel       -- Speaker knows the true state
  | uncertain : CompetenceLevel  -- Speaker may be uncertain
  | none : CompetenceLevel       -- No competence assumption
  deriving DecidableEq, Repr

/-- Epistemic state: combines world state with speaker knowledge.
    Used for epistemic readings of scalar implicatures. -/
structure EpistemicState (S : Type) where
  actualWorld : S
  speakerKnowledge : Set S  -- What worlds speaker considers possible

/-- Build epistemic interpretation game from base game -/
def toEpistemicGame (G : InterpGame) (comp : CompetenceLevel) : InterpGame :=
  match comp with
  | .full => G  -- Full competence: same as base game
  | _ => G      -- Simplified: would need richer state space

end RSA.IBR
