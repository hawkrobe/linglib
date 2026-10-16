module

public import Mathlib.Tactic.TypeStar

/-!
# Evaluating accounts against data

This library evaluates the accounts that linglib formalizes against the data it records. An
account's verdict on an observation is right, wrong, or silent when the account predicts nothing
about it or nothing was observed (`Eval.Verdict`). A verdict is always derived from the account's
own definitions and the recorded data, and the comparison it makes is fixed by the type of the
prediction, never by a label attached to an account or a datum.

An experiment is scored cell by cell (`Eval.Experiment`): it records the outcome observed in each
cell of its design, and its linking hypothesis says what outcome a theory predicts there. The
verdict on a theory in a cell compares the two (`Experiment.verdict`). Whatever a theory brings to
the comparison, such as how it parses the experiment's sentences, is part of what is scored, so
that the cells are the facts alone.
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

/-- An experiment scoring theories `Θ`, with cells `C` and outcomes `O`: the outcome observed in
each cell, and the outcome its linking hypothesis has a theory predict there. -/
structure Experiment (Θ C O : Type*) where
  /-- The outcome observed in a cell, if the cell was run. -/
  observed : C → Option O
  /-- The outcome a theory predicts in a cell by the linking hypothesis, if it predicts one. -/
  predicted : Θ → C → Option O

/-- The verdict on a theory in a cell of an experiment. -/
def Experiment.verdict {Θ C O : Type*} [DecidableEq O] (X : Experiment Θ C O) (T : Θ) (c : C) :
    Verdict :=
  .of (X.predicted T c) (X.observed c)

end Eval
