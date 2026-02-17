/-
Shared infrastructure for RSA models of question-answer pragmatics.

## References

- Hawkins, R.D., et al. (2025). Relevant answers to polar questions.
- Van Rooy, R. (2003). Questioning to Resolve Decision Problems. L&P 26.
- Groenendijk, J. & Stokhof, M. (1984). Studies on the Semantics of Questions.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring
import Linglib.Theories.Pragmatics.RSA.Core.Distribution
import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility

namespace RSA.Questions

open RSA.Eval

/-- Expected value of a distribution -/
def expectedValue {α : Type} (f : α → ℚ) (dist : List (α × ℚ)) : ℚ :=
  dist.foldl (λ acc (a, p) => acc + f a * p) 0

def combinedUtility := RSA.CombinedUtility.combined

/-- RSA question-answer model parameters. -/
structure Params where
  /-- Questioner rationality -/
  αQ : ℚ := 5
  /-- Respondent rationality -/
  αR : ℚ := 5
  /-- Action-relevance weight: 0 = informativity, 1 = action-relevance -/
  β : ℚ := 1/2
  /-- Response cost weight -/
  costWeight : ℚ := 3/10
  deriving Repr, BEq

/-- Default parameters (Hawkins et al. 2025) -/
def defaultParams : Params := {}

def pureInformativityParams : Params := { defaultParams with β := 0 }

def pureActionRelevanceParams : Params := { defaultParams with β := 1 }

/-- Generic response type: taciturn, elaborated, or exhaustive. -/
inductive GenericResponse (Info : Type) where
  | taciturn : Bool → GenericResponse Info
  | withInfo : Bool → Info → GenericResponse Info
  | exhaustive : Bool → List Info → GenericResponse Info
  deriving Repr

def GenericResponse.answer {Info : Type} : GenericResponse Info → Bool
  | .taciturn b => b
  | .withInfo b _ => b
  | .exhaustive b _ => b

def GenericResponse.cost {Info : Type} (r : GenericResponse Info) : ℚ :=
  match r with
  | .taciturn _ => 1
  | .withInfo _ _ => 2
  | .exhaustive _ items => 1 + items.length

/-- Van Rooy's UV(C) = V(D|C) - V(D). -/
def informationValue (valueBefore valueAfter : ℚ) : ℚ :=
  valueAfter - valueBefore

/-- Informativity as inverse of response set size. -/
def basicInformativity (responseSetSize : Nat) : ℚ :=
  if responseSetSize == 0 then 0 else 1 / responseSetSize

/-- β = 0 yields pure informativity. -/
theorem beta_tradeoff (params : Params) :
    params.β = 0 → (1 - params.β) = 1 ∧ params.β = 0 := by
  intro h
  constructor
  · rw [h]; norm_num
  · exact h

/-- Softmax function for utilities -/
def softmax (α : ℚ) (utilities : List ℚ) : List ℚ :=
  let scores := utilities.map λ u => max 0 (1 + α * u)
  let total := RSA.Eval.sumScores scores
  if total == 0 then utilities.map (λ _ => 0)
  else scores.map (λ s => s / total)

/-- Softmax preserves list length. -/
@[simp] theorem softmax_length (α : ℚ) (utilities : List ℚ) :
    (softmax α utilities).length = utilities.length := by
  simp only [softmax]
  split_ifs <;> simp only [List.length_map]

/-- Sum of n ones is n (generalized over accumulator for foldl). -/
private theorem foldl_add_ones (acc : ℚ) :
    ∀ (l : List ℚ), (l.map fun _ => (1 : ℚ)).foldl (· + ·) acc = acc + ↑l.length
  | [] => by simp
  | _ :: l => by
    simp only [List.map_cons, List.foldl_cons, List.length_cons, Nat.cast_succ]
    rw [foldl_add_ones (acc + 1) l]; ring

/-- Softmax with α=0 gives uniform distribution. -/
theorem softmax_uniform_limit (utilities : List ℚ) (hne : utilities.length > 0) :
    softmax 0 utilities = utilities.map (λ _ => (1 : ℚ) / ↑utilities.length) := by
  simp only [softmax, zero_mul, add_zero, max_eq_right zero_le_one]
  have hsum : RSA.Eval.sumScores (utilities.map fun _ => (1 : ℚ)) = ↑utilities.length := by
    simp only [RSA.Eval.sumScores]
    exact (foldl_add_ones 0 utilities).trans (by simp)
  rw [hsum]
  have hne' : (↑utilities.length : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  split_ifs with h
  · exact absurd (beq_iff_eq.mp h) hne'
  · simp only [List.map_map, Function.comp_def]

/-- Higher α concentrates softmax on highest utility. -/
theorem softmax_concentration (alpha1 alpha2 : ℚ) (utilities : List ℚ)
    (h : alpha1 < alpha2) :
    True := by trivial  -- TODO: state the actual concentration property

end RSA.Questions
