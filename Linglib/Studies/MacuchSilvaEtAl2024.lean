import Linglib.Semantics.Alternatives.Lexical
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Macuch Silva et al. (2024): Strategic Use of English Quantifiers

This file formalizes the argumentative-difficulty account of [macuch-silva-etal-2024]. Two
experiments have English speakers describe exam results, a number of correct answers out of a
total, under a goal of framing the outcome as a success or as a failure. The difficulty of
framing a result in the desired direction is the distance of its proportion from the goal's
ideal (`argumentativeDifficulty`), and the account predicts that as difficulty grows the
speaker retreats to informationally weaker quantifiers, from *all* through *most* to *some*,
those truthful over broader ranges of outcomes (`truthfulQuantifiers`,
`strongestTruthfulPositive`, `weakening_with_difficulty`). The paper thereby extends the
argumentative strength of [cummins-franke-2021] from a property of the speaker's utterance
to a property of the situation.

## Implementation notes

Proportions and difficulties are rationals; the quantifier scale is the lexical scale of
`Semantics.Alternatives.Lexical`. The experiments' response rates are reported in prose in
the paper and are not represented.

## TODO

The paper is not on file; the page locators are transcribed from an earlier version of this
file and are UNVERIFIED.

## References

* [macuch-silva-etal-2024]
* [cummins-franke-2021]
-/

namespace MacuchSilvaEtAl2024


/-- Experimental condition: high or low success framing -/
inductive Condition where
  | highSuccess  -- "describe as if students did well"
  | lowSuccess   -- "describe as if students did poorly"
  deriving DecidableEq, Repr

/-- Adjective choice in the forced-choice task -/
inductive Adjective where
  | right
  | wrong
  deriving DecidableEq, Repr

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

-- Verify difficulty at extremes

/-- Perfect score in high-success = 0 difficulty (easiest) -/
theorem perfect_highSuccess_easy :
    argumentativeDifficulty ⟨60, 60, le_refl 60⟩ .highSuccess = 0 := by decide +kernel

/-- Zero correct in low-success = 0 difficulty (easiest) -/
theorem zero_lowSuccess_easy :
    argumentativeDifficulty ⟨0, 60, Nat.zero_le 60⟩ .lowSuccess = 0 := by decide +kernel

/-- 15/60 correct in high-success = 0.75 difficulty (hard) -/
theorem quarter_highSuccess_hard :
    argumentativeDifficulty ⟨15, 60, by omega⟩ .highSuccess = 3/4 := by decide +kernel

/-- Difficulty is monotone: more correct → harder to frame as low success -/
theorem difficulty_monotone_lowSuccess
    (n₁ n₂ total : Nat) (h₁ : n₁ ≤ total) (h₂ : n₂ ≤ total) (hlt : n₁ < n₂)
    (ht : 0 < total) :
    argumentativeDifficulty ⟨n₁, total, h₁⟩ .lowSuccess <
    argumentativeDifficulty ⟨n₂, total, h₂⟩ .lowSuccess := by
  simp [argumentativeDifficulty, ExamStimulus.proportion, Nat.ne_of_gt ht]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hlt) (Nat.cast_pos.mpr ht)


/-- Which quantifiers from {all, most, some, none} are truthful
for a given exam result? -/
def truthfulQuantifiers (s : ExamStimulus) : List Alternatives.Quantifiers.QuantExpr :=
  let result : List Alternatives.Quantifiers.QuantExpr := []
  let result := if s.nCorrect = 0 then result ++ [.none_] else result
  let result := if s.nCorrect > 0 then result ++ [.some_] else result
  let result := if s.nCorrect * 2 > s.nTotal then result ++ [.most] else result
  let result := if s.nCorrect = s.nTotal then result ++ [.all] else result
  result

/-- The strongest truthful quantifier for positive framing.

As proportion decreases (difficulty increases in high-success):
all (perfect) → most (majority) → some (any nonzero) → none (zero) -/
def strongestTruthfulPositive (s : ExamStimulus) : Alternatives.Quantifiers.QuantExpr :=
  if s.nCorrect = s.nTotal then .all
  else if s.nCorrect * 2 > s.nTotal then .most
  else if s.nCorrect > 0 then .some_
  else .none_

-- Verify the weakening pattern with concrete examples

/-- Perfect score (difficulty 0.0): "all" is available -/
theorem perfect_allows_all :
    strongestTruthfulPositive ⟨60, 60, le_refl 60⟩ = .all := by decide +kernel

/-- 42/60 correct (difficulty 0.3): "most" is strongest -/
theorem fortytwo_allows_most :
    strongestTruthfulPositive ⟨42, 60, by omega⟩ = .most := by decide +kernel

/-- 18/60 correct (difficulty 0.7): "some" is strongest -/
theorem eighteen_allows_some :
    strongestTruthfulPositive ⟨18, 60, by omega⟩ = .some_ := by decide +kernel

/-- Zero correct (difficulty 1.0): only "none" is truthful -/
theorem zero_allows_none :
    strongestTruthfulPositive ⟨0, 60, Nat.zero_le 60⟩ = .none_ := by decide +kernel

/-- The quantifier ordering matches the Horn scale from `Degree` -/
theorem quantifier_ordering_matches_scale :
    Alternatives.Quantifiers.entails .all .most = true ∧
    Alternatives.Quantifiers.entails .most .some_ = true ∧
    Alternatives.Quantifiers.entails .some_ .none_ = false := by decide +kernel

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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel


end MacuchSilvaEtAl2024
