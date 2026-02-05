import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic

/-!
# Basic Question Types

Core types for question semantics shared across theoretical approaches.

## Main definitions

`Question`, `Answer`, `Cell`, `exactQuestion`, `questionProduct`, `answers`

## References

-/

namespace Montague.Question

/-- Partition-based question: list of mutually exclusive proposition cells. -/
abbrev Question (W : Type*) := List (W -> Bool)

/-- Answer: proposition as characteristic function on worlds. -/
abbrev Answer (W : Type*) := W -> Bool

/-- Cell in a question partition. -/
abbrev Cell (W : Type*) := W -> Bool

def trivialQuestion {W : Type*} : Question W := [λ _ => true]

def exactQuestion {W : Type*} [DecidableEq W] (worlds : List W) : Question W :=
  worlds.map λ w => λ v => w == v

def numCells {W : Type*} (q : Question W) : Nat := q.length

def consistentWith {W : Type*} (p : Answer W) (cell : Cell W) (worlds : List W) : Bool :=
  worlds.any λ w => p w && cell w

def cellOf {W : Type*} (q : Question W) (w : W) : Option (Cell W) :=
  q.find? λ cell => cell w

def filterWorlds {W : Type*} (worlds : List W) (p : W -> Bool) : List W :=
  worlds.filter p

/-- Product of two questions: cells are intersections. -/
def questionProduct {W : Type*} (q1 q2 : Question W) : Question W :=
  q1.flatMap λ c1 => q2.map λ c2 => λ w => c1 w && c2 w

instance {W : Type*} : Mul (Question W) where
  mul := questionProduct

/-- Join of two questions: coarsest refinement of both. -/
def questionJoin {W : Type*} (q1 q2 : Question W) (worlds : List W) : Question W :=
  let equiv := λ w v =>
    (q1.any λ c => c w && c v) && (q2.any λ c => c w && c v)
  let reps := worlds.foldl (λ acc w =>
    if acc.any λ r => equiv r w then acc else w :: acc) []
  reps.map λ rep => λ w => equiv rep w

def answers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  q.any λ cell => worlds.all λ w => p w -> cell w

def partiallyAnswers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  let overlapping := q.filter λ cell => worlds.any λ w => p w && cell w
  overlapping.length > 0 && overlapping.length < q.length

def completelyAnswers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  let overlapping := q.filter λ cell => worlds.any λ w => p w && cell w
  overlapping.length == 1

def pnot {W : Type*} (p : W -> Bool) : W -> Bool := λ w => !p w

def pand {W : Type*} (p q : W -> Bool) : W -> Bool := λ w => p w && q w

def por {W : Type*} (p q : W -> Bool) : W -> Bool := λ w => p w || q w

def pimplies {W : Type*} (p q : W -> Bool) : W -> Bool := λ w => !p w || q w

def entails {W : Type*} (p q : W -> Bool) (worlds : List W) : Bool :=
  worlds.all λ w => !p w || q w

end Montague.Question
