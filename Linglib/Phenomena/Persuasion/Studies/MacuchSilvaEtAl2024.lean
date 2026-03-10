import Linglib.Theories.Pragmatics.RSA.Extensions.ArgumentativeStrength
import Linglib.Theories.Pragmatics.RSA.Quantities
import Linglib.Core.Scales.HornScale
import Mathlib.Data.Rat.Defs

/-!
# @cite{macuch-silva-etal-2024}: Strategic Use of English Quantifiers
@cite{macuch-silva-etal-2024} @cite{cummins-franke-2021}

Formalizes Macuch Silva, Lorson, Franke, Cummins & Winter (2024) "Strategic use
of English quantifiers in the reporting of quantitative information",
*Discourse Processes* 61(10), 498–523.

Two experiments on how English speakers strategically choose quantifiers
to describe school exam results under positive or negative framing goals.

## Experiment 1 — Forced Choice (p. 503)

60 participants each saw all 20 exam-result tables (5 students × 12 questions)
and completed "In this exam [Q1] of the students got [Q2] of the questions [ADJ]"
with Q1, Q2 ∈ {all, most, some, none} and ADJ ∈ {right, wrong}.
Within-subjects: each participant saw 10 stimuli in high-success framing
and 10 in low-success (allocation randomized).

## Experiment 2 — Free Production (p. 510)

30 participants wrote free-form descriptions of 12 stimuli under the same
framing manipulation. Responses coded for expression type, negation, and polarity.

## Key Results

1. **Adjective choice tracks condition**: 92% "right" in high success, 18% in low
2. **some/most dominate**: 78% (high) / 74% (low) of quantifier choices
3. **Positive framing bias**: 74% of Exp 2 descriptions framed positively
4. **Difficulty → weakening**: as argumentative difficulty increases,
   speakers shift from all → most → some

## Theoretical Contribution

The *argumentative difficulty* metric captures how hard it is to frame a
quantitative result in a given direction. When difficulty is high (e.g.,
framing bad results positively), speakers use informationally weaker
quantifiers that are truthful over broader ranges of outcomes.
This extends @cite{cummins-franke-2021}'s argumentative strength framework
from speaker-oriented argStr to a situation-oriented difficulty measure.

-/

namespace Phenomena.Persuasion.Studies.MacuchSilvaEtAl2024

open RSA.ArgumentativeStrength
open RSA.Domains.Quantity


-- ============================================================
-- Section 1: Experimental Design
-- ============================================================

/-- Experimental condition: high or low success framing -/
inductive Condition where
  | highSuccess  -- "describe as if students did well"
  | lowSuccess   -- "describe as if students did poorly"
  deriving DecidableEq, BEq, Repr

/-- Adjective choice in the forced-choice task -/
inductive Adjective where
  | right
  | wrong
  deriving DecidableEq, BEq, Repr

/-- An exam stimulus: nCorrect out of nTotal cells are green (correct).
Each table has 5 students × 12 questions = 60 cells. -/
structure ExamStimulus where
  nCorrect : Nat
  nTotal : Nat
  h_le : nCorrect ≤ nTotal
  deriving Repr

/-- Proportion correct as a rational -/
def ExamStimulus.proportion (s : ExamStimulus) : ℚ :=
  if s.nTotal = 0 then 0
  else ↑s.nCorrect / ↑s.nTotal


-- ============================================================
-- Section 2: Argumentative Difficulty (pp. 501–502, 507)
-- ============================================================

/-- Argumentative difficulty: how hard it is to frame a result in the desired direction.

High-success condition: difficulty = 1 - proportion
  (easy when all correct → 0.0, hard when few correct → 1.0)
Low-success condition: difficulty = proportion
  (easy when none correct → 0.0, hard when many correct → 1.0)

This is the simplified version. The paper also uses a refined metric
accounting for distribution shape across students (p. 507), but the
ordinal predictions are the same. -/
def argumentativeDifficulty (s : ExamStimulus) (c : Condition) : ℚ :=
  let p := s.proportion
  match c with
  | .highSuccess => 1 - p
  | .lowSuccess => p

/-- Wrap as an ArgumentativeDifficulty from the theory layer -/
def toArgDifficulty (s : ExamStimulus) (c : Condition) : ArgumentativeDifficulty :=
  { proportion := s.proportion
    isPositiveFrame := c == .highSuccess
    difficulty := argumentativeDifficulty s c }

-- Verify difficulty at extremes

/-- Perfect score in high-success = 0 difficulty (easiest) -/
theorem perfect_highSuccess_easy :
    argumentativeDifficulty ⟨60, 60, le_refl 60⟩ .highSuccess = 0 := by native_decide

/-- Zero correct in low-success = 0 difficulty (easiest) -/
theorem zero_lowSuccess_easy :
    argumentativeDifficulty ⟨0, 60, Nat.zero_le 60⟩ .lowSuccess = 0 := by native_decide

/-- 15/60 correct in high-success = 0.75 difficulty (hard) -/
theorem quarter_highSuccess_hard :
    argumentativeDifficulty ⟨15, 60, by omega⟩ .highSuccess = 3/4 := by native_decide

/-- Difficulty is monotone: more correct → harder to frame as low success -/
theorem difficulty_monotone_lowSuccess
    (n₁ n₂ total : Nat) (h₁ : n₁ ≤ total) (h₂ : n₂ ≤ total) (hlt : n₁ < n₂)
    (ht : 0 < total) :
    argumentativeDifficulty ⟨n₁, total, h₁⟩ .lowSuccess <
    argumentativeDifficulty ⟨n₂, total, h₂⟩ .lowSuccess := by
  simp [argumentativeDifficulty, ExamStimulus.proportion, Nat.ne_of_gt ht]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hlt) (Nat.cast_pos.mpr ht)


-- ============================================================
-- Section 3: Quantifier Weakening Prediction
-- ============================================================

/-- Which quantifiers from {all, most, some, none} are truthful
for a given exam result? -/
def truthfulQuantifiers (s : ExamStimulus) : List ExtUtterance :=
  let result : List ExtUtterance := []
  let result := if s.nCorrect = 0 then result ++ [.none_] else result
  let result := if s.nCorrect > 0 then result ++ [.some_] else result
  let result := if s.nCorrect * 2 > s.nTotal then result ++ [.most] else result
  let result := if s.nCorrect = s.nTotal then result ++ [.all] else result
  result

/-- The strongest truthful quantifier for positive framing.

As proportion decreases (difficulty increases in high-success):
all (perfect) → most (majority) → some (any nonzero) → none (zero) -/
def strongestTruthfulPositive (s : ExamStimulus) : ExtUtterance :=
  if s.nCorrect = s.nTotal then .all
  else if s.nCorrect * 2 > s.nTotal then .most
  else if s.nCorrect > 0 then .some_
  else .none_

-- Verify the weakening pattern with concrete examples

/-- Perfect score (difficulty 0.0): "all" is available -/
theorem perfect_allows_all :
    strongestTruthfulPositive ⟨60, 60, le_refl 60⟩ = .all := by native_decide

/-- 42/60 correct (difficulty 0.3): "most" is strongest -/
theorem fortytwo_allows_most :
    strongestTruthfulPositive ⟨42, 60, by omega⟩ = .most := by native_decide

/-- 18/60 correct (difficulty 0.7): "some" is strongest -/
theorem eighteen_allows_some :
    strongestTruthfulPositive ⟨18, 60, by omega⟩ = .some_ := by native_decide

/-- Zero correct (difficulty 1.0): only "none" is truthful -/
theorem zero_allows_none :
    strongestTruthfulPositive ⟨0, 60, Nat.zero_le 60⟩ = .none_ := by native_decide

/-- The quantifier ordering matches the Horn scale from Core.Scale -/
theorem quantifier_ordering_matches_scale :
    Core.Scale.Quantifiers.entails .all .most = true ∧
    Core.Scale.Quantifiers.entails .most .some_ = true ∧
    Core.Scale.Quantifiers.entails .some_ .none_ = false := by native_decide

/-- The weakening pattern: increasing difficulty leads to weaker
strongest-truthful quantifier. Demonstrated for high-success framing. -/
theorem weakening_with_difficulty :
    -- difficulty 0.0: all
    strongestTruthfulPositive ⟨60, 60, le_refl 60⟩ = .all ∧
    -- difficulty 0.17: most (high success, most students did well)
    strongestTruthfulPositive ⟨50, 60, by omega⟩ = .most ∧
    -- difficulty 0.5: most (half correct, still majority)
    strongestTruthfulPositive ⟨31, 60, by omega⟩ = .most ∧
    -- difficulty 0.7: some (minority correct)
    strongestTruthfulPositive ⟨18, 60, by omega⟩ = .some_ ∧
    -- difficulty 1.0: none (zero correct)
    strongestTruthfulPositive ⟨0, 60, Nat.zero_le 60⟩ = .none_ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide


-- ============================================================
-- Section 4: Experiment 1 Results (p. 505)
-- ============================================================

/-- Adjective choice: 92% chose "right" in high-success condition.
(β = 0.99, 95% CrI [0.96, 1.0]; p. 505) -/
def exp1_adjective_rate_highSuccess : ℚ := 92 / 100

/-- Adjective choice: 18% chose "right" in low-success condition.
(β = 0.10, 95% CrI [0.05, 0.17]; p. 505)
Note: β = 0.10 is the model's posterior probability, not the observed rate. -/
def exp1_adjective_rate_lowSuccess : ℚ := 18 / 100

/-- Adjective choice strongly matches framing condition -/
theorem exp1_adjective_matches_condition :
    exp1_adjective_rate_highSuccess > 3/4 ∧
    exp1_adjective_rate_lowSuccess < 1/4 := by
  constructor <;> native_decide

/-- Quantifier proportions for student reference (p. 505).
"some and most are the quantifiers most frequently used to refer to students" -/
structure Exp1QuantifierData where
  condition : String
  someRate : ℚ
  mostRate : ℚ
  deriving Repr

def exp1_quant_highSuccess : Exp1QuantifierData :=
  { condition := "high success", someRate := 38/100, mostRate := 40/100 }

def exp1_quant_lowSuccess : Exp1QuantifierData :=
  { condition := "low success", someRate := 38/100, mostRate := 36/100 }

/-- some + most dominate quantifier choices in both conditions -/
theorem exp1_some_most_dominant :
    exp1_quant_highSuccess.someRate + exp1_quant_highSuccess.mostRate > 1/2 ∧
    exp1_quant_lowSuccess.someRate + exp1_quant_lowSuccess.mostRate > 1/2 := by
  constructor <;> native_decide

/-- some + most combined rates -/
def exp1_some_most_highSuccess : ℚ := 78 / 100  -- 38% + 40%
def exp1_some_most_lowSuccess : ℚ := 74 / 100   -- 38% + 36%

/-- Quantifier proportions for question reference (p. 505).
"most and all referring to questions" -/
def exp1_questions_highSuccess_most : ℚ := 41 / 100
def exp1_questions_highSuccess_all : ℚ := 36 / 100
def exp1_questions_lowSuccess_most : ℚ := 39 / 100
def exp1_questions_lowSuccess_all : ℚ := 33 / 100

/-- most + all dominate question-reference quantifiers -/
theorem exp1_questions_most_all_dominant :
    exp1_questions_highSuccess_most + exp1_questions_highSuccess_all > 1/2 ∧
    exp1_questions_lowSuccess_most + exp1_questions_lowSuccess_all > 1/2 := by
  constructor <;> native_decide


-- ============================================================
-- Section 5: Experiment 2 Results (pp. 512–515)
-- ============================================================

/-- Experiment 2: 330 total descriptions, 265 analyzed (pp. 511–512).
64 excluded for containing multiple student/question references. -/
def exp2_totalDescriptions : Nat := 330
def exp2_analyzedDescriptions : Nat := 265

/-- Positive framing bias: 74% across conditions (p. 514).

High success: 98% positive; Low success: 51% negative.
Even in the low-success condition, ~49% still framed positively. -/
def exp2_positive_bias_rate : ℚ := 74 / 100
def exp2_highSuccess_positive_rate : ℚ := 98 / 100
def exp2_lowSuccess_negative_rate : ℚ := 51 / 100

theorem exp2_positive_bias :
    exp2_positive_bias_rate > 1/2 := by native_decide

/-- High-success overwhelmingly positive; low-success roughly split -/
theorem exp2_framing_asymmetry :
    exp2_highSuccess_positive_rate > 9/10 ∧
    exp2_lowSuccess_negative_rate < 6/10 := by
  constructor <;> native_decide

/-- Expression strategy categories (p. 512).
Based on which referents (students, questions) receive quantity expressions. -/
structure ExpressionStrategy where
  strategy : String
  proportion : ℚ
  deriving Repr

/-- Experiment 2 strategy proportions (p. 512) -/
def exp2_strategies : List ExpressionStrategy :=
  [ ⟨"student + question quantity",  55 / 100⟩
  , ⟨"student quantity only",        33 / 100⟩
  , ⟨"no quantity expression",        9 / 100⟩
  , ⟨"question quantity only",        3 / 100⟩
  ]

/-- Strategy proportions sum to 100% -/
theorem exp2_strategies_sum :
    (55 : ℚ)/100 + 33/100 + 9/100 + 3/100 = 1 := by native_decide

/-- Dual-reference (student + question) is the most common strategy -/
theorem exp2_dual_most_common :
    (55 : ℚ)/100 > 33/100 := by native_decide

/-- Among responses with quantifiers (151 observations; p. 515):
all, most, some, none account for 67%; all + most = 54%. -/
def exp2_standard_quantifier_share : ℚ := 67 / 100
def exp2_all_most_share : ℚ := 54 / 100

theorem exp2_standard_quantifiers_dominant :
    exp2_standard_quantifier_share > 1/2 ∧
    exp2_all_most_share > 1/2 := by
  constructor <;> native_decide

/-- Most prevalent cross-condition strategies (p. 515):
20% use quantifiers for both referents,
19% use quantifier for students only. -/
def exp2_both_quantifiers_rate : ℚ := 20 / 100
def exp2_student_quantifier_only_rate : ℚ := 19 / 100

theorem exp2_top_strategies_close :
    exp2_both_quantifiers_rate > exp2_student_quantifier_only_rate := by native_decide


-- ============================================================
-- Section 6: Difficulty Modulates Quantifier Choice (pp. 517–519)
-- ============================================================

/-- Core finding: difficulty modulates quantifier choice (p. 519).

When framing matches condition (e.g., "right" in high success):
- Difficulty ~0.0: *all* most likely
- Difficulty ~0.25: *most* overtakes *all*
- Difficulty ~0.50: *some* overtakes *most*
- Difficulty ~0.75: *none* overtakes *some* (for negative framing)

This matches the weakening prediction: speakers use informationally
weaker quantifiers when the situation is hard to frame in the
desired direction (p. 519). -/
structure DifficultyQuantifierPrediction where
  difficultyThreshold : ℚ
  dominantBefore : ExtUtterance
  dominantAfter : ExtUtterance
  deriving Repr

/-- Approximate crossover thresholds from Figures 5–6 and 10–11.
These are read from density plots and are approximate. -/
def exp1_crossovers_highSuccess_right : List DifficultyQuantifierPrediction :=
  [ ⟨25/100, .all, .most⟩     -- all → most at ~0.25 difficulty
  , ⟨50/100, .most, .some_⟩   -- most → some at ~0.50 difficulty
  ]

/-- The crossover pattern matches the Horn scale ordering:
at each threshold, the dominant quantifier shifts one step down. -/
theorem crossovers_follow_horn_scale :
    Core.Scale.Quantifiers.entails .all .most = true ∧
    Core.Scale.Quantifiers.entails .most .some_ = true := by native_decide


end Phenomena.Persuasion.Studies.MacuchSilvaEtAl2024
