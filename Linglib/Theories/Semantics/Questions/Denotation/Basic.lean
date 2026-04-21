import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Linglib.Tactics.OntSort

/-!
# Basic Question Types

Core types for question semantics shared across theoretical approaches.
-/

namespace Semantics.Questions

/-- Partition-based question: list of mutually exclusive proposition cells. -/
@[ont_sort] abbrev Question (W : Type*) := List (W -> Bool)

/-- Answer: proposition as characteristic function on worlds. -/
abbrev Answer (W : Type*) := W -> Bool

/-- Cell in a question partition. -/
abbrev Cell (W : Type*) := W -> Bool

def exactQuestion {W : Type*} [DecidableEq W] (worlds : List W) : Question W :=
  worlds.map λ w => λ v => w == v

def answers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  q.any λ cell => worlds.all λ w => p w -> cell w

def completelyAnswers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  let overlapping := q.filter λ cell => worlds.any λ w => p w && cell w
  overlapping.length == 1

def pnot {W : Type*} (p : W -> Bool) : W -> Bool := λ w => !p w

def entails {W : Type*} (p q : W -> Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !p w || q w

end Semantics.Questions
