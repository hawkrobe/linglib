import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic

/-!
# Questions/Basic.lean

Core types for question semantics, shared across different theoretical approaches.

## Contents

- `Question`: A partition-based question (list of mutually exclusive cells)
- `Answer`: A proposition that resolves a question
- Basic operations on questions and answers
-/

namespace Montague.Question

-- ============================================================================
-- Core Types
-- ============================================================================

/-- A partition-based question: list of mutually exclusive propositions (cells).

Each cell represents one possible complete answer to the question.
The cells should partition the world space (mutually exclusive, jointly exhaustive). -/
abbrev Question (W : Type*) := List (W -> Bool)

/-- An answer is a proposition (characteristic function on worlds). -/
abbrev Answer (W : Type*) := W -> Bool

/-- A cell in a question partition -/
abbrev Cell (W : Type*) := W -> Bool

-- ============================================================================
-- Basic Operations
-- ============================================================================

/-- The trivial question (one cell containing everything) -/
def trivialQuestion {W : Type*} : Question W := [fun _ => true]

/-- The maximally fine question given a world list -/
def exactQuestion {W : Type*} [DecidableEq W] (worlds : List W) : Question W :=
  worlds.map fun w => fun v => w == v

/-- Number of cells in a question -/
def numCells {W : Type*} (q : Question W) : Nat := q.length

/-- Check if a proposition is consistent with a cell -/
def consistentWith {W : Type*} (p : Answer W) (cell : Cell W) (worlds : List W) : Bool :=
  worlds.any fun w => p w && cell w

/-- The cell that a world belongs to -/
def cellOf {W : Type*} (q : Question W) (w : W) : Option (Cell W) :=
  q.find? fun cell => cell w

/-- Filter worlds by a proposition -/
def filterWorlds {W : Type*} (worlds : List W) (p : W -> Bool) : List W :=
  worlds.filter p

-- ============================================================================
-- Question Composition
-- ============================================================================

/-- Product of two questions: cells are intersections.
The resulting question is at least as fine as both inputs. -/
def questionProduct {W : Type*} (q1 q2 : Question W) : Question W :=
  q1.flatMap fun c1 => q2.map fun c2 => fun w => c1 w && c2 w

instance {W : Type*} : Mul (Question W) where
  mul := questionProduct

/-- Join of two questions: coarsest refinement of both.
Result is the finest question that both q1 and q2 refine. -/
def questionJoin {W : Type*} (q1 q2 : Question W) (worlds : List W) : Question W :=
  -- Two worlds are equivalent iff equivalent under both questions
  let equiv := fun w v =>
    (q1.any fun c => c w && c v) && (q2.any fun c => c w && c v)
  -- Build cells from equivalence classes
  let reps := worlds.foldl (fun acc w =>
    if acc.any fun r => equiv r w then acc else w :: acc) []
  reps.map fun rep => fun w => equiv rep w

-- ============================================================================
-- Question Answerhood
-- ============================================================================

/-- A proposition p answers question q if p is contained in some cell -/
def answers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  q.any fun cell => worlds.all fun w => p w -> cell w

/-- A proposition p partially answers q if p overlaps with multiple cells -/
def partiallyAnswers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  let overlapping := q.filter fun cell => worlds.any fun w => p w && cell w
  overlapping.length > 0 && overlapping.length < q.length

/-- A proposition p completely answers q if p selects exactly one cell -/
def completelyAnswers {W : Type*} (p : Answer W) (q : Question W) (worlds : List W) : Bool :=
  let overlapping := q.filter fun cell => worlds.any fun w => p w && cell w
  overlapping.length == 1

-- ============================================================================
-- Propositional Operations
-- ============================================================================

/-- Negation of a proposition -/
def pnot {W : Type*} (p : W -> Bool) : W -> Bool := fun w => !p w

/-- Conjunction of propositions -/
def pand {W : Type*} (p q : W -> Bool) : W -> Bool := fun w => p w && q w

/-- Disjunction of propositions -/
def por {W : Type*} (p q : W -> Bool) : W -> Bool := fun w => p w || q w

/-- Implication -/
def pimplies {W : Type*} (p q : W -> Bool) : W -> Bool := fun w => !p w || q w

/-- Entailment: p entails q iff p ⊆ q -/
def entails {W : Type*} (p q : W -> Bool) (worlds : List W) : Bool :=
  worlds.all fun w => !p w || q w

end Montague.Question
