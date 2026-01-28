/-
# Scontras & Tonhauser (2025): Projection Experimental Data

Empirical findings from "Projection without lexically-specified presupposition:
A model for know" (SuB 29).

## Experiments

- Exp 1: n=873, 6 utterances × 2 QUDs × 2 priors
- Exp 2: n=327, 4 utterances × 2 QUDs (stronger QUD manipulation)

## Key Effects

All three hypothesized effects were confirmed:
(a) know > think in projection
(b) higher prior > lower prior
(c) BEL? QUD > C? QUD (only in Exp 2 with stronger manipulation)
-/

namespace Phenomena.Projection.ScontrasTonhauser2025

-- ============================================================================
-- Regression Coefficients (Tables 1 & 2)
-- ============================================================================

/-- Effect of utterance type: negated know vs negated think (Exp 1) -/
structure UtteranceEffect where
  β : Float      -- regression coefficient
  se : Float     -- standard error
  t : Float      -- t-value
  p : Float      -- p-value
  deriving Repr

/-- Exp 1: Utterance effect (know > think) -/
def exp1_utteranceEffect : UtteranceEffect :=
  { β := 0.35, se := 0.03, t := 12.2, p := 0.001 }

/-- Exp 1: Prior effect (higher > lower) -/
def exp1_priorEffect : UtteranceEffect :=
  { β := 0.16, se := 0.03, t := 5.5, p := 0.001 }

/-- Exp 1: QUD effect (NOT significant - manipulation too weak) -/
def exp1_qudEffect : UtteranceEffect :=
  { β := 0.009, se := 0.03, t := 0.3, p := 0.75 }

/-- Exp 2: Utterance effect (know > think) -/
def exp2_utteranceEffect : UtteranceEffect :=
  { β := 0.34, se := 0.04, t := 8.8, p := 0.001 }

/-- Exp 2: QUD effect (significant with stronger manipulation) -/
def exp2_qudEffect : UtteranceEffect :=
  { β := 0.14, se := 0.04, t := 3.6, p := 0.001 }

-- ============================================================================
-- Summary: Empirical Hypotheses
-- ============================================================================

/-- The three empirical hypotheses and their support -/
inductive Hypothesis where
  | utterance  -- (a) know > think
  | prior      -- (b) higher > lower prior
  | qud        -- (c) BEL? > C?
  deriving DecidableEq, Repr

/-- Whether hypothesis was supported in each experiment -/
def supported : Hypothesis → Bool × Bool  -- (Exp1, Exp2)
  | .utterance => (true, true)   -- Supported in both
  | .prior     => (true, true)   -- Supported in Exp1 (not tested in Exp2)
  | .qud       => (false, true)  -- Only in Exp2 (stronger manipulation)

/-- Effect direction matches prediction -/
def directionCorrect : Hypothesis → Bool
  | .utterance => exp1_utteranceEffect.β > 0  -- know > think
  | .prior     => exp1_priorEffect.β > 0      -- higher > lower
  | .qud       => exp2_qudEffect.β > 0        -- BEL? > C?

-- All directions match predictions
example : directionCorrect .utterance = true := by native_decide
example : directionCorrect .prior = true := by native_decide
example : directionCorrect .qud = true := by native_decide

end Phenomena.Projection.ScontrasTonhauser2025
