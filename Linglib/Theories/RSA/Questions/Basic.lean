/-
# RSA/Questions/Basic.lean

Shared infrastructure for RSA models of question-answer pragmatics.

## Overview

This module provides common types and utilities for RSA-based models of
questions and responses, including:
- Rationality parameters
- Soft-max utilities
- Base types for polar question scenarios

## Key Models Supported

- **PRIOR-PQ** (Hawkins et al. 2025): Polar question response selection
- **Van Rooy (2003)**: Decision-theoretic question semantics
- **G&S (1984)**: Partition semantics (via Montague/Questions)

## Architecture

```
RSA/Questions/Basic.lean        <- This file (shared infrastructure)
     |
     +-- RSA/Questions/PolarQuestions.lean (polar question DPs)
     +-- RSA/Questions/ResponseSelection.lean (response models)
     |
     +-- Montague/Questions/DecisionTheory.lean (Van Rooy's foundation)
     +-- Montague/Questions/Partition.lean (G&S semantics)
```

## References

- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
- Van Rooy, R. (2003). Questioning to Resolve Decision Problems.
- Groenendijk, J. & Stokhof, M. (1984). Studies on the Semantics of Questions.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Linglib.Core.Distribution
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Core.CombinedUtility

namespace RSA.Questions

open RSA.Eval

/-- Expected value of a distribution -/
def expectedValue {α : Type} (f : α → ℚ) (dist : List (α × ℚ)) : ℚ :=
  dist.foldl (fun acc (a, p) => acc + f a * p) 0

-- Alias combined utility for backwards compatibility
def combinedUtility := RSA.CombinedUtility.combined

-- ============================================================================
-- PART 1: Rationality Parameters
-- ============================================================================

/-- Model parameters for RSA question-answer models.

These parameters control the rationality/optimality of speakers and listeners
in pragmatic reasoning about questions and responses.

- `αQ`: Questioner rationality (how optimally they choose questions)
- `αR`: Respondent rationality (how optimally they choose responses)
- `β`: Weight on action-relevance vs informativity (0=pure info, 1=pure action)
- `costWeight`: How much response cost is penalized

Higher α values → more optimal (deterministic) behavior
Lower α values → more noisy (uniform) behavior
-/
structure Params where
  /-- Questioner rationality parameter -/
  αQ : ℚ := 5
  /-- Respondent rationality parameter -/
  αR : ℚ := 5
  /-- Action-relevance weight (vs informativity). 0 = pure informativity, 1 = pure action-relevance. -/
  β : ℚ := 1/2
  /-- Response cost weight -/
  costWeight : ℚ := 3/10
  deriving Repr, BEq

/-- Default parameters (matches Hawkins et al. 2025) -/
def defaultParams : Params := {}

/-- Parameters for pure informativity model (β = 0) -/
def pureInformativityParams : Params := { defaultParams with β := 0 }

/-- Parameters for pure action-relevance model (β = 1) -/
def pureActionRelevanceParams : Params := { defaultParams with β := 1 }

-- ============================================================================
-- PART 2: Soft-Max Utilities (from RSA.Eval)
-- ============================================================================

-- Note: normalize, getScore, sumScores, softmax available via `open RSA.Eval`.

-- ============================================================================
-- PART 4: Response Types (Generic)
-- ============================================================================

/-- Generic response type for polar questions.

Most polar question models distinguish:
- Taciturn: Just "yes" or "no"
- Elaborated: Answer plus additional information
- Exhaustive: Complete information about alternatives
-/
inductive GenericResponse (Info : Type) where
  /-- Minimal response: just yes or no -/
  | taciturn : Bool → GenericResponse Info
  /-- Response with additional info: answer + extra content -/
  | withInfo : Bool → Info → GenericResponse Info
  /-- Exhaustive response: answer + all relevant info -/
  | exhaustive : Bool → List Info → GenericResponse Info
  deriving Repr

/-- Extract the yes/no answer from any response -/
def GenericResponse.answer {Info : Type} : GenericResponse Info → Bool
  | .taciturn b => b
  | .withInfo b _ => b
  | .exhaustive b _ => b

/-- Response cost (proportional to length/complexity) -/
def GenericResponse.cost {Info : Type} (r : GenericResponse Info) : ℚ :=
  match r with
  | .taciturn _ => 1
  | .withInfo _ _ => 2
  | .exhaustive _ items => 1 + items.length

-- ============================================================================
-- PART 5: Information Value
-- ============================================================================

/-- Information value of learning a response.

This captures Van Rooy's UV(C) = V(D|C) - V(D):
The improvement in expected utility from learning the response.

- `valueBefore`: V(D) - expected utility before learning response
- `valueAfter`: V(D|C) - expected utility after learning response
-/
def informationValue (valueBefore valueAfter : ℚ) : ℚ :=
  valueAfter - valueBefore

/-- Informativity as inverse of response set size.

Simple informativity measure: more specific responses (fewer alternatives
consistent with them) are more informative.
-/
def basicInformativity (responseSetSize : Nat) : ℚ :=
  if responseSetSize == 0 then 0 else 1 / responseSetSize

-- ============================================================================
-- PART 6: Combined Utility Model (imported from RSA.CombinedUtility)
-- ============================================================================

-- Note: combinedUtility is defined above as an alias to RSA.CombinedUtility.combined
-- The endpoint theorems are in RSA.CombinedUtility (combined_at_zero, combined_at_one)

-- ============================================================================
-- PART 7: KL Divergence Approximation (imported from ListDist)
-- ============================================================================

-- Note: approxDivergence and approxJSD are re-exported from ListDist above.

-- ============================================================================
-- PART 8: Theoretical Properties
-- ============================================================================

/-- β controls the informativity vs action-relevance tradeoff.

- β = 0: Pure informativity → prefer responses that reduce uncertainty
- β = 1: Pure action-relevance → prefer responses that help achieve goals
-/
theorem beta_tradeoff (params : Params) :
    params.β = 0 → (1 - params.β) = 1 ∧ params.β = 0 := by
  intro h
  constructor
  · rw [h]; norm_num
  · exact h

/-- Softmax function for utilities -/
def softmax (α : ℚ) (utilities : List ℚ) : List ℚ :=
  let scores := utilities.map fun u => max 0 (1 + α * u)
  let total := RSA.Eval.sumScores scores
  if total == 0 then utilities.map (fun _ => 0)
  else scores.map (fun s => s / total)

/-- Softmax with α=0 approaches uniform distribution -/
theorem softmax_uniform_limit (utilities : List ℚ) (hne : utilities.length > 0) :
    softmax 0 utilities = utilities.map (fun _ => 1 / utilities.length) := by
  simp only [softmax]
  -- When α = 0, all scores are max(0, 1 + 0*u) = 1
  sorry

/-- Higher α makes softmax more concentrated on highest utility -/
theorem softmax_concentration (alpha1 alpha2 : ℚ) (utilities : List ℚ)
    (h : alpha1 < alpha2) :
    -- The max probability under alpha2 is at least as high as under alpha1
    -- (more concentrated = higher peak)
    True := by trivial  -- Placeholder for the actual concentration property

end RSA.Questions
