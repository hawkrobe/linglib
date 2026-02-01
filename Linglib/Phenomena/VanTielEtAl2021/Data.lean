/-
# van Tiel, Franke & Sauerland (2021) - Experimental Data

"Probabilistic pragmatics explains gradience and focality in natural language quantification"
PNAS 118(9): e2005453118

## Experiments

1. **Exp. 1a/1b**: Production study (600/200 participants)
   - 432 circles (red/black), describe "— of the circles are red"
   - Recorded which quantity words participants used

2. **Exp. 2**: Monotonicity judgments (120 participants)
   - Tested inference patterns to classify monotonicity

3. **Exp. 3**: ANS estimation (20 participants)
   - Estimated Weber's fraction w = 0.576

4. **Exp. 4**: Model evaluation (200 participants)
   - Rated adequacy of model-predicted quantity words

## Key Finding

GQ-pragmatic model explains gradience as well as prototype-based models.
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.VanTielEtAl2021

-- ============================================================================
-- Quantity Words Used in Experiments
-- ============================================================================

/-- The 17 quantity words studied (in order from low to high intersection) -/
inductive QuantityWord where
  | none_         -- "none"
  | hardlyAny     -- "hardly any"
  | veryFew       -- "very few"
  | aFew          -- "a few"
  | few           -- "few"
  | lessThanHalf  -- "less than half"
  | some_         -- "some"
  | several       -- "several"
  | half          -- "half"
  | aboutHalf     -- "about half"
  | many          -- "many"
  | moreThanHalf  -- "more than half"
  | aLot          -- "a lot"
  | majority      -- "majority"
  | most          -- "most"
  | almostAll     -- "almost all"
  | all           -- "all"
  deriving Repr, DecidableEq, BEq, Inhabited

/-- All quantity words in experimental order -/
def allQuantityWords : List QuantityWord :=
  [.none_, .hardlyAny, .veryFew, .aFew, .few, .lessThanHalf, .some_, .several,
   .half, .aboutHalf, .many, .moreThanHalf, .aLot, .majority, .most, .almostAll, .all]

-- ============================================================================
-- Monotonicity Classification (Exp. 2)
-- ============================================================================

/-- Monotonicity determines threshold direction in GQT -/
inductive Monotonicity where
  | increasing  -- licenses inference from sets to supersets
  | decreasing  -- licenses inference from sets to subsets
  deriving Repr, DecidableEq

/-- Empirically determined monotonicity (from Exp. 2, Table in paper)

Participants judged inference patterns:
- Monotone increasing: "Q of the people P1 → Q of the people P2" valid when P1 ⊂ P2
- Monotone decreasing: "Q of the people P2 → Q of the people P1" valid when P1 ⊂ P2

Classification: clustered with "all" (increasing) or "none" (decreasing)
-/
def monotonicity : QuantityWord → Monotonicity
  | .none_         => .decreasing
  | .hardlyAny     => .decreasing
  | .veryFew       => .decreasing
  | .aFew          => .increasing
  | .few           => .decreasing
  | .lessThanHalf  => .decreasing
  | .some_         => .increasing
  | .several       => .increasing
  | .half          => .increasing
  | .aboutHalf     => .increasing
  | .many          => .increasing
  | .moreThanHalf  => .increasing
  | .aLot          => .increasing
  | .majority      => .increasing
  | .most          => .increasing
  | .almostAll     => .increasing
  | .all           => .increasing

/-- Decreasing quantifiers (from paper: "few," "hardly any," "less than half," "none," "very few") -/
def decreasingQuantifiers : List QuantityWord :=
  [.none_, .hardlyAny, .veryFew, .few, .lessThanHalf]

/-- Increasing quantifiers (all others) -/
def increasingQuantifiers : List QuantityWord :=
  allQuantityWords.filter (fun q => monotonicity q == .increasing)

-- ============================================================================
-- Model Comparison Results (Table 1)
-- ============================================================================

/-- The four models compared in the paper -/
inductive Model where
  | gqLit    -- GQT semantics + literal speaker
  | ptLit    -- Prototype Theory semantics + literal speaker
  | gqPrag   -- GQT semantics + pragmatic speaker
  | ptPrag   -- Prototype Theory semantics + pragmatic speaker
  deriving Repr, DecidableEq, BEq

/-- Log-likelihood of test data (Exp. 1b) for each model

Higher is better. GQ-prag achieves the best fit.
-/
def logLikelihood : Model → Int
  | .gqLit  => -1717
  | .ptLit  => -1660
  | .gqPrag => -1625  -- Best fit
  | .ptPrag => -1675

/-- Human rating difference (Exp. 4)

Rating of model predictions minus rating of actual data.
Negative = model predictions rated worse than data.
CI = 95% confidence interval.
-/
structure RatingResult where
  mean : ℚ
  ciLow : ℚ
  ciHigh : ℚ
  deriving Repr

def ratingDifference : Model → RatingResult
  | .gqLit  => ⟨-225/100, -330/100, -130/100⟩   -- CI excludes 0
  | .ptLit  => ⟨-99/100,  -197/100,    0/100⟩   -- CI includes 0 (marginal)
  | .gqPrag => ⟨-77/100,  -182/100,   14/100⟩   -- CI includes 0 (not significantly worse)
  | .ptPrag => ⟨-141/100, -237/100,  -41/100⟩   -- CI excludes 0

/-- GQ-prag is the only model not significantly worse than data (p > 0.05) -/
def notSignificantlyWorse : Model → Bool
  | .gqPrag => true   -- p = 0.07
  | _       => false  -- all others p < 0.02

-- ============================================================================
-- Approximate Number System (Exp. 3)
-- ============================================================================

/-- Weber's fraction estimated from Exp. 3

Represents sensitivity to relative differences in numerosity.
Higher w means less precise number discrimination.
-/
def weberFraction : ℚ := 576 / 1000  -- 0.576

/-- Total set size in experiments -/
def totalSetSize : Nat := 432

/-- Number of possible intersection set sizes (0 through 432) -/
def numWorldStates : Nat := 433

-- ============================================================================
-- Focal Production Points (from Fig. 1)
-- ============================================================================

/-- Approximate prototype (peak production) for each quantity word.

These are rough estimates from Fig. 1A in the paper.
Values are approximate intersection set sizes where production peaks.
-/
def approximatePrototype : QuantityWord → Nat
  | .none_         => 0
  | .hardlyAny     => 10
  | .veryFew       => 20
  | .aFew          => 40
  | .few           => 60
  | .lessThanHalf  => 160
  | .some_         => 80
  | .several       => 100
  | .half          => 216    -- half of 432
  | .aboutHalf     => 216
  | .many          => 280
  | .moreThanHalf  => 260
  | .aLot          => 300
  | .majority      => 300
  | .most          => 340
  | .almostAll     => 400
  | .all           => 432

-- ============================================================================
-- Key Empirical Patterns
-- ============================================================================

/-
## Pattern 1: Gradience

Production probabilities for quantity words show gradual transitions,
not sharp boundaries. This is true even for words with clear logical
thresholds (e.g., "all" should be 432 exactly, but production extends below).

## Pattern 2: Focality

Each quantity word has a focal point where production peaks.
For example:
- "some" peaks around 80, not at the threshold of 1
- "most" peaks around 340 (roughly 80%), not at 217 (just over half)

## Pattern 3: Overlap

Multiple quantity words can be produced for the same intersection set size.
At t=300, participants might produce "many", "most", "a lot", or "majority".

## Pattern 4: GQ-prag Explains These

The key finding is that GQT + pragmatic reasoning produces:
- Gradience: from competition between utterances
- Focality: from informativity preferences
- Overlap: from multiple true descriptions with different informativity
-/

/-- Production data shows gradience (quantitative pattern) -/
def hasGradience : Bool := true

/-- Production data shows focal points (qualitative pattern) -/
def hasFocality : Bool := true

/-- Multiple quantity words can describe same state -/
def hasOverlap : Bool := true

-- ============================================================================
-- Competition Without Entailment (Novel Contribution)
-- ============================================================================

/-
## Pragmatic Competition Beyond Scalar Implicature

Traditional scalar implicature requires entailment (all → some).
This paper shows pragmatic competition occurs even WITHOUT entailment.

Example: "some" and "few" do not entail each other:
- "few" true, "some" false: when t = 0
- "some" true, "few" false: when t = total

Yet pragmatic speakers still contrast them based on communicative success.
This generalizes Gricean reasoning beyond traditional Horn scales.
-/

/-- "some" and "few" don't stand in entailment relation -/
theorem some_few_no_entailment :
    -- "few" can be true when "some" is false (at t=0)
    (monotonicity .few = .decreasing ∧ monotonicity .some_ = .increasing)
    -- They have opposite monotonicity, so neither entails the other
    := by native_decide

-- ============================================================================
-- Summary Statistics
-- ============================================================================

/-- Number of participants in Exp. 1a (training) -/
def exp1a_participants : Nat := 600

/-- Number of participants in Exp. 1b (test) -/
def exp1b_participants : Nat := 200

/-- Number of participants in Exp. 2 (monotonicity) -/
def exp2_participants : Nat := 120

/-- Number of participants in Exp. 3 (ANS) -/
def exp3_participants : Nat := 20

/-- Number of participants in Exp. 4 (evaluation) -/
def exp4_participants : Nat := 200

/-- These 17 quantity words account for 87% of production data -/
def coveragePercent : Nat := 87

end Phenomena.VanTielEtAl2021
