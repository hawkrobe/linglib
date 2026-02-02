/-
# Grusdt, Lassiter & Franke (2022)

"Probabilistic modeling of rational communication with conditionals"

## Overview

This paper extends RSA to model conditionals by:
1. Treating "worlds" as probability distributions (WorldState)
2. Using assertability (P(C|A) > θ) as the literal meaning of conditionals
3. Having L1 infer both the world state AND the causal structure

## Key Innovation: WorldState as the "World"

Unlike standard RSA where worlds are atomic states, here a "world" is itself
a probability distribution over atomic propositions A and C. This is because
conditionals make claims about conditional probabilities, not atomic truth values.

## The Model

**Utterances**: Literals (A, C, ¬A, ¬C), conjunction (A∧C), conditional (if A then C),
likely phrases (likely A, likely C, etc.)

**World States**: Distributions parameterized by (pA, pC, pAC)

**Causal Relations**: The listener infers whether A→C, C→A, or A⊥C

**L0**: Samples world states where the utterance is assertable
  - For conditionals: P(C|A) > θ

**S1**: Chooses utterances to communicate world state (and causal relation)

**L1**: Infers both world state AND causal relation from utterance

## Grounding

The meaning of conditionals is grounded in the assertability condition from
`Montague.Sentence.Conditional.Assertability`:

```
L0_conditional_meaning = conditionalSemantics
```

## References

- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals. PLoS ONE.
-/

import Mathlib.Data.Rat.Defs
import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Core.CausalBayesNet
import Linglib.Theories.Montague.Sentence.Conditional.Assertability

namespace RSA.GrusdtLassiterFranke2022

open Core.CausalBayesNet
open RSA.Eval
open Montague.Sentence.Conditional.Assertability

-- ============================================================================
-- Utterance Types
-- ============================================================================

/--
Literal propositions about A and C.
-/
inductive Literal
  | A     -- "A" (the antecedent)
  | C     -- "C" (the consequent)
  | notA  -- "not A"
  | notC  -- "not C"
  deriving Repr, DecidableEq, BEq

instance : ToString Literal where
  toString
    | .A => "A"
    | .C => "C"
    | .notA => "¬A"
    | .notC => "¬C"

/--
Utterance types from the paper.

The speaker can utter:
1. Bare literals: "A", "C", "not A", "not C"
2. Conjunction: "A and C"
3. Conditional: "if A then C"
4. Likely phrases: "likely A", "likely C", etc.
5. Silence (null utterance)
-/
inductive Utterance
  | literal : Literal → Utterance           -- A, C, ¬A, ¬C
  | conj                                    -- A ∧ C
  | conditional                             -- if A then C
  | likely : Literal → Utterance            -- likely A, likely C, etc.
  | likelyConditional                       -- likely if A then C
  | silence                                 -- null utterance
  deriving Repr, DecidableEq, BEq

instance : ToString Utterance where
  toString
    | .literal l => toString l
    | .conj => "A ∧ C"
    | .conditional => "if A then C"
    | .likely l => s!"likely {l}"
    | .likelyConditional => "likely (if A then C)"
    | .silence => "∅"

-- ============================================================================
-- Assertability Thresholds
-- ============================================================================

/--
Threshold for conditional assertability.

The paper uses θ = 0.9 as the default.
-/
def conditionalThreshold : ℚ := 9/10

/--
Threshold for "likely X" assertability.

P(X) must exceed this threshold.
-/
def likelyThreshold : ℚ := 7/10

-- ============================================================================
-- Utterance Semantics
-- ============================================================================

/--
Literal semantics: when is a literal assertable?

- A: P(A) > 0.9 (high probability)
- C: P(C) > 0.9
- ¬A: P(¬A) > 0.9 (i.e., P(A) < 0.1)
- ¬C: P(¬C) > 0.9 (i.e., P(C) < 0.1)

For soft semantics, we return the probability directly.
-/
def literalSemantics (l : Literal) (ws : WorldState) (θ : ℚ := likelyThreshold) : ℚ :=
  match l with
  | .A => if ws.pA > θ then 1 else 0
  | .C => if ws.pC > θ then 1 else 0
  | .notA => if 1 - ws.pA > θ then 1 else 0
  | .notC => if 1 - ws.pC > θ then 1 else 0

/--
Soft literal semantics: return the probability itself.
-/
def softLiteralSemantics (l : Literal) (ws : WorldState) : ℚ :=
  match l with
  | .A => ws.pA
  | .C => ws.pC
  | .notA => 1 - ws.pA
  | .notC => 1 - ws.pC

/--
Conjunction semantics: P(A ∧ C) > θ
-/
def conjunctionSemantics (ws : WorldState) (θ : ℚ := likelyThreshold) : ℚ :=
  if ws.pAC > θ then 1 else 0

/--
Soft conjunction semantics: return P(A ∧ C)
-/
def softConjunctionSemantics (ws : WorldState) : ℚ :=
  ws.pAC

/--
Conditional semantics: P(C|A) > θ (from Montague.Sentence.Conditional.Assertability)

This is the grounding: we use the assertability condition directly.
-/
def conditionalSemanticsHard (ws : WorldState) (θ : ℚ := conditionalThreshold) : ℚ :=
  conditionalSemantics ws θ

/--
Soft conditional semantics: return P(C|A) (from Assertability module)
-/
def conditionalSemanticsSoft (ws : WorldState) : ℚ :=
  softConditionalSemantics ws

/--
"Likely" semantics: the embedded proposition has high probability
-/
def likelySemantics (l : Literal) (ws : WorldState) (θ : ℚ := likelyThreshold) : ℚ :=
  let prob := softLiteralSemantics l ws
  if prob > θ then 1 else 0

/--
"Likely conditional" semantics
-/
def likelyConditionalSemantics (ws : WorldState) (θ : ℚ := likelyThreshold) : ℚ :=
  let prob := conditionalSemanticsSoft ws
  if prob > θ then 1 else 0

/--
Full utterance semantics (hard version with thresholds).
-/
def utteranceSemantics (u : Utterance) (ws : WorldState)
    (condθ : ℚ := conditionalThreshold) (likelyθ : ℚ := likelyThreshold) : ℚ :=
  match u with
  | .literal l => literalSemantics l ws likelyθ
  | .conj => conjunctionSemantics ws likelyθ
  | .conditional => conditionalSemanticsHard ws condθ
  | .likely l => likelySemantics l ws likelyθ
  | .likelyConditional => likelyConditionalSemantics ws likelyθ
  | .silence => 1  -- Silence is always "true"

/--
Soft utterance semantics (for gradient RSA).
-/
def softUtteranceSemantics (u : Utterance) (ws : WorldState) : ℚ :=
  match u with
  | .literal l => softLiteralSemantics l ws
  | .conj => softConjunctionSemantics ws
  | .conditional => conditionalSemanticsSoft ws
  | .likely l => softLiteralSemantics l ws  -- Same as literal for soft
  | .likelyConditional => conditionalSemanticsSoft ws
  | .silence => 1/2  -- Uninformative

-- ============================================================================
-- World State Space (Discretized)
-- ============================================================================

/--
Discretized probability levels for computational tractability.
-/
def probLevels : List ℚ := [0, 1/4, 1/2, 3/4, 1]

/--
Check if (pA, pC, pAC) form a valid probability distribution.
-/
def isValidTriple (pA pC pAC : ℚ) : Bool :=
  0 ≤ pA && pA ≤ 1 &&
  0 ≤ pC && pC ≤ 1 &&
  0 ≤ pAC && pAC ≤ min pA pC &&
  pA + pC - pAC ≤ 1

/--
Generate all valid discretized world states.
-/
def allWorldStates : List WorldState :=
  probLevels.flatMap fun pA =>
    probLevels.flatMap fun pC =>
      probLevels.filterMap fun pAC =>
        if isValidTriple pA pC pAC then
          some { pA := pA, pC := pC, pAC := pAC }
        else none

-- ============================================================================
-- Causal Inference
-- ============================================================================

/--
The full meaning space: WorldState × CausalRelation

The listener infers both:
1. The probability distribution (WorldState)
2. The underlying causal structure (CausalRelation)
-/
abbrev FullMeaning := WorldState × CausalRelation

/--
All causal relations.
-/
def allCausalRelations : List CausalRelation :=
  [.ACausesC, .CCausesA, .Independent]

/--
All full meanings (world states × causal relations).
-/
def allFullMeanings : List FullMeaning :=
  allWorldStates.flatMap fun ws =>
    allCausalRelations.map fun cr => (ws, cr)

-- ============================================================================
-- Priors
-- ============================================================================

/--
Prior over world states.

The paper uses a uniform prior over valid distributions.
-/
def worldStatePrior (_ws : WorldState) : ℚ := 1

/--
Prior over causal relations.

The paper assumes equal prior on all three relations.
-/
def causalRelationPrior (_cr : CausalRelation) : ℚ := 1

/--
Prior over full meanings.
-/
def fullMeaningPrior (m : FullMeaning) : ℚ :=
  worldStatePrior m.1 * causalRelationPrior m.2

-- ============================================================================
-- Goal/QUD Projection
-- ============================================================================

/--
Goal type: what is the listener trying to infer?

Following the paper, we consider:
1. `worldState`: Infer the probability distribution
2. `causalRelation`: Infer the causal structure
3. `both`: Infer both
-/
inductive Goal
  | worldState
  | causalRelation
  | both
  deriving Repr, DecidableEq, BEq

def allGoals : List Goal := [.worldState, .causalRelation, .both]

/--
Goal projection: when are two full meanings equivalent under a goal?
-/
def goalProject (g : Goal) (m1 m2 : FullMeaning) : Bool :=
  match g with
  | .worldState => m1.1 == m2.1
  | .causalRelation => m1.2 == m2.2
  | .both => m1 == m2

-- ============================================================================
-- Utterance Cost
-- ============================================================================

/--
Utterance cost (length-based).

Longer/more complex utterances are costlier.
-/
def utteranceCost : Utterance → ℚ
  | .literal _ => 1
  | .conj => 2
  | .conditional => 3
  | .likely _ => 2
  | .likelyConditional => 4
  | .silence => 0

-- ============================================================================
-- RSA Computations
-- ============================================================================

def allUtterances : List Utterance :=
  [.literal .A, .literal .C, .literal .notA, .literal .notC,
   .conj, .conditional,
   .likely .A, .likely .C, .likely .notA, .likely .notC,
   .likelyConditional, .silence]

/--
L0: Literal listener distribution over full meanings given an utterance.

P_L0(m | u) ∝ Prior(m) · ⟦u⟧(ws)

Note: The semantics only depends on the world state, not the causal relation.
But L0 returns a distribution over full meanings for consistency with L1.
-/
def L0 (u : Utterance) : List (FullMeaning × ℚ) :=
  let scores := allFullMeanings.map fun m =>
    let sem := utteranceSemantics u m.1
    (m, fullMeaningPrior m * sem)
  normalize scores

/--
L0 marginalized over causal relations: distribution over world states only.
-/
def L0_world (u : Utterance) : List (WorldState × ℚ) :=
  let l0 := L0 u
  marginalize l0 (·.1)

/--
S1: Pragmatic speaker given a full meaning and goal.

P_S1(u | m, g) ∝ exp(α · log P_L0_projected(m | u) - cost(u))
-/
def S1 (m : FullMeaning) (g : Goal) (α : ℕ := 1) : List (Utterance × ℚ) :=
  let scores := allUtterances.map fun u =>
    let l0 := L0 u
    -- Project L0 according to goal
    let projectedScore :=
      l0.filter (fun (m', _) => goalProject g m m') |>.map (·.2) |> sumScores
    let costDiscount := 1 / ((1 + utteranceCost u) ^ α)
    (u, (projectedScore ^ α) * costDiscount)
  normalize scores

/--
L1: Pragmatic listener distribution over full meanings given an utterance.

P_L1(m | u) ∝ Prior(m) · P_S1(u | m)

L1 marginalizes over possible goals.
-/
def L1 (u : Utterance) (α : ℕ := 1) : List (FullMeaning × ℚ) :=
  let scores := allFullMeanings.flatMap fun m =>
    allGoals.map fun g =>
      let s1 := S1 m g α
      let s1Score := getScore s1 u
      (m, fullMeaningPrior m * s1Score)
  -- Sum over goals for each meaning
  let combined := allFullMeanings.map fun m =>
    let totalScore := scores.filter (fun (m', _) => m' == m) |>.map (·.2) |> sumScores
    (m, totalScore)
  normalize combined

/--
L1 marginalized over causal relations: distribution over world states only.
-/
def L1_world (u : Utterance) (α : ℕ := 1) : List (WorldState × ℚ) :=
  let l1 := L1 u α
  marginalize l1 (·.1)

/--
L1 marginalized over world states: distribution over causal relations only.

This is the key prediction: from a conditional utterance, L1 infers the
most likely causal structure.
-/
def L1_causalRelation (u : Utterance) (α : ℕ := 1) : List (CausalRelation × ℚ) :=
  let l1 := L1 u α
  marginalize l1 (·.2)

-- ============================================================================
-- Grounding Theorem
-- ============================================================================

/--
**Grounding Theorem**: L0 conditional meaning equals Montague assertability.

The RSA model's literal listener interprets conditionals using the
assertability condition from `Montague.Sentence.Conditional.Assertability`.

This proves that the RSA model is grounded in compositional semantics.
-/
theorem conditional_grounding (ws : WorldState) :
    utteranceSemantics .conditional ws = conditionalSemantics ws := by
  rfl

/--
**Grounding Theorem (Soft)**: Soft conditional meaning equals conditional probability.
-/
theorem conditional_grounding_soft (ws : WorldState) :
    softUtteranceSemantics .conditional ws = softConditionalSemantics ws := by
  rfl

-- ============================================================================
-- Key Predictions
-- ============================================================================

/--
**Prediction 1**: Conditional perfection emerges pragmatically.

When L1 hears "if A then C", they infer A→C causal structure.
Given A→C, they expect "if ¬A then ¬C" would NOT be assertable.
This is conditional perfection as an implicature.
-/
def conditionalPerfectionPrediction : Bool :=
  let l1Causal := L1_causalRelation .conditional
  -- Expect A→C to have highest probability
  getScore l1Causal .ACausesC > getScore l1Causal .Independent

/--
**Prediction 2**: Missing-link conditionals are dispreferred.

S1 is unlikely to utter "if A then C" when A⊥C (independent).
-/
def missingLinkDispreferred : Bool :=
  -- An independent world state
  let indepWs : WorldState := WorldState.independentExample
  let s1 := S1 (indepWs, .Independent) .both
  -- Expect conditional to have low probability
  getScore s1 .conditional < getScore s1 .silence

-- ============================================================================
-- Evaluation
-- ============================================================================

#eval L0_world .conditional
-- L0 given "if A then C": should prefer high P(C|A) world states

#eval L1_causalRelation .conditional
-- L1 causal inference: should prefer A→C over independent

#eval conditionalPerfectionPrediction
-- Expected: true

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## How the Model Works

1. **World States as Distributions**: Unlike standard RSA, "worlds" are
   probability distributions over atomic propositions A and C.

2. **Assertability-Based Semantics**: The literal meaning of "if A then C"
   is that P(C|A) > θ (high conditional probability).

3. **Causal Inference**: L1 jointly infers the world state AND the causal
   relation (A→C, C→A, or A⊥C) from the utterance.

4. **Conditional Perfection**: Emerges because "if A then C" is informative
   about A→C causation, which implies "if ¬A then ¬C" would not be assertable.

5. **Missing-Link Infelicity**: S1 avoids conditionals when A⊥C because
   they provide little information about the causal structure.

## Key Design Decisions

1. **WorldState as meaning**: The paper's key insight is that conditionals
   communicate about probability distributions, not atomic facts.

2. **Causal relation as Goal**: We use RSAScenario's Goal slot to represent
   the causal relation that L1 infers.

3. **Grounding in Assertability**: The conditional semantics is exactly
   the assertability condition from Montague.Sentence.Conditional.

## References

- Grusdt, Lassiter & Franke (2022). Probabilistic modeling of rational
  communication with conditionals. PLoS ONE.
- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
-/

end RSA.GrusdtLassiterFranke2022
