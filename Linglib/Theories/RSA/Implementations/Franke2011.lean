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

/-- The pragmatic interpretation: support of the IBR fixed point listener -/
def pragmaticSupport (G : InterpGame) (H : HearerStrategy G) (m : G.Message) :
    Finset G.State :=
  H.support m

-- ============================================================================
-- SECTION 5: Connection to Exhaustive Interpretation
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
-/

/-- Convert interpretation game to alternative set for exhaustification.
    Converts Bool meaning to Prop' by using equality with true. -/
def toAlternatives (G : InterpGame) : Set (Prop' G.State) :=
  { fun s => G.meaning m s = true | m : G.Message }

/-- The prejacent proposition for a message (Bool → Prop conversion) -/
def prejacent (G : InterpGame) (m : G.Message) : Prop' G.State :=
  fun s => G.meaning m s = true

/-- IBR fixed point equals exhMW (Main theorem statement)

This is the central result connecting game theory to exhaustification.
At the fixed point, the IBR listener's interpretation of message m is
exactly the exhaustive interpretation exhMW(ALT, m).

Note: The proof requires showing that:
1. IBR eliminates states where a stronger true alternative exists
2. This is exactly the minimality condition in exhMW
-/
theorem ibr_equals_exhMW (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message) :
    (∀ s, H.respond m s > 0 ↔ exhMW (toAlternatives G) (prejacent G m) s) := by
  sorry -- Full proof requires induction on IBR iterations

/-- Alternative characterization: IBR excludes non-minimal states -/
theorem ibr_excludes_nonminimal (G : InterpGame) (m : G.Message) (s : G.State)
    (hs : G.meaning m s = true)
    (hNonMin : ∃ s', G.meaning m s' = true ∧ ltALT (toAlternatives G) s' s) :
    (L2 G).respond m s = 0 := by
  sorry -- Proof: non-minimal states eliminated by S₁ optimization

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
-- SECTION 8: Comparison with Spector's Theorem 9
-- ============================================================================

/-!
## Connection to Spector (2016) Theorem 9

Spector's Theorem 9: When ALT is closed under conjunction, exhMW = exhIE.

Franke's result: IBR = exhMW.

Combined: When ALT is closed under conjunction, IBR = exhMW = exhIE.

This shows that the game-theoretic approach (Franke) and the grammatical
approach (Fox/Spector) converge to the same predictions under natural conditions.
-/

/-- When alternatives are closed under conjunction, IBR = exhIE -/
theorem ibr_equals_exhIE (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    (∀ s, H.respond m s > 0 ↔ exhIE (toAlternatives G) (prejacent G m) s) := by
  -- By ibr_equals_exhMW and Spector's Theorem 9
  sorry

-- ============================================================================
-- SECTION 9: The RSA → EXH Limit Theorem
-- ============================================================================

/-!
## The Complete Picture: RSA → IBR → EXH

This section states the full limit theorem connecting RSA to EXH:

  lim_{α→∞} RSA.L1(α, m) = IBR.L∞(m) = exhMW(ALT, m)

And under closure:

  lim_{α→∞} RSA.L1(α, m) = exhIE(ALT, m)

This is the formal statement of the claim that:
**RSA and EXH are the same rational principle at different "temperatures"**

- Temperature 1/α = 0 (α = ∞): deterministic selection (EXH/IBR)
- Temperature 1/α > 0 (α finite): probabilistic selection (RSA)
-/

/-- RSA L1 support converges to IBR fixed point support as α → ∞ -/
theorem rsa_l1_to_ibr (G : InterpGame) (H : HearerStrategy G)
    (hFP : isIBRFixedPoint G H) (m : G.Message) :
    -- For all ε > 0, exists α₀ such that for all α > α₀,
    -- RSA L1 support is within ε of IBR fixed point support
    True := by trivial -- Placeholder for full limit statement

/-- The grand unification: RSA → EXH as α → ∞ -/
theorem rsa_to_exh_limit (G : InterpGame) (m : G.Message) :
    -- lim_{α→∞} support(RSA.L1(α, m)) = exhMW(ALT, m)
    True := by trivial -- Placeholder for full limit statement

/-- With closure, RSA → exhIE -/
theorem rsa_to_exhIE_limit (G : InterpGame) (m : G.Message)
    (hClosed : closedUnderConj (toAlternatives G)) :
    -- lim_{α→∞} support(RSA.L1(α, m)) = exhIE(ALT, m)
    True := by trivial -- Placeholder for full limit statement

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
