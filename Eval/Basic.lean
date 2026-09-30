module

public import Mathlib.Tactic.TypeStar

/-!
# Evaluating accounts against data

This library evaluates the accounts that linglib formalizes against the data it records. An
account's verdict on an observation is right, wrong, or silent when the account predicts nothing
about it or nothing was observed (`Eval.Verdict`). A verdict is always derived from the account's
own definitions and the recorded data, and the comparison it makes is fixed by the type of the
prediction, never by a label attached to an account or a datum.
-/

@[expose] public section

namespace Eval

/-- An account's verdict on an observation. -/
inductive Verdict where
  /-- The prediction matches the observation. -/
  | correct
  /-- The prediction differs from the observation. -/
  | wrong
  /-- The account predicts nothing, or nothing was observed. -/
  | silent
  deriving DecidableEq, Repr

/-- The verdict of a prediction on an observation of the same type. -/
def Verdict.of {α : Type*} [DecidableEq α] : Option α → Option α → Verdict
  | some p, some o => if p = o then .correct else .wrong
  | _, _ => .silent

end Eval
