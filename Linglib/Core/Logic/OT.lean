import Linglib.Core.Logic.ConstraintEvaluation

/-!
# Optimality Theory — Core Vocabulary

OT-specific vocabulary layered on `Core.Logic.ConstraintEvaluation`. Provides
named constraints with a faithfulness/markedness distinction, convenience
constructors for building tableaux from ranked constraint lists, and factorial
typology computation.

## Connection to ConstraintEvaluation

`ConstraintEvaluation` provides the generic engine (`lexLE`, `OTTableau`,
`OTTableau.optimal`). This module adds OT-specific structure: constraint
families, named constraints, and the factorial typology pattern (enumerate
all rankings, compute optima, count distinct outcomes).
-/

namespace Core.OT

open Core.ConstraintEvaluation

-- ============================================================================
-- § 1: Named Constraints
-- ============================================================================

/-- Constraint families in OT. -/
inductive ConstraintFamily where
  /-- Faithfulness: penalizes deviation from the input. -/
  | faithfulness
  /-- Markedness: penalizes marked structures in the output. -/
  | markedness
  deriving DecidableEq, BEq, Repr

/-- A named OT constraint with family classification.
    `eval c` returns the number of violations candidate `c` incurs. -/
structure NamedConstraint (C : Type) where
  name : String
  family : ConstraintFamily
  eval : C → Nat

-- ============================================================================
-- § 2: Tableau Construction
-- ============================================================================

/-- Build a violation profile from a ranked list of named constraints.
    Position 0 = highest-ranked constraint. -/
def buildProfile {C : Type} (ranking : List (NamedConstraint C)) (c : C) : List Nat :=
  ranking.map fun con => con.eval c

/-- Build an OT tableau from a candidate list and a constraint ranking. -/
def buildTableau {C : Type} (candidates : List C)
    (ranking : List (NamedConstraint C))
    (h : candidates ≠ []) : OTTableau C :=
  { candidates := candidates
  , profile := buildProfile ranking
  , nonempty := h }

-- ============================================================================
-- § 3: Permutations (for factorial typology)
-- ============================================================================

/-- Insert element `a` at every position in list `l`. -/
private def insertEverywhere {α : Type} (a : α) : List α → List (List α)
  | [] => [[a]]
  | x :: xs =>
    (a :: x :: xs) :: (insertEverywhere a xs).map (x :: ·)

/-- All permutations of a list. -/
def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (permutations xs).flatMap (insertEverywhere x)

-- ============================================================================
-- § 4: Factorial Typology
-- ============================================================================

/-- For each permutation of `constraints`, compute the set of optimal
    candidates. Return the list of distinct optimal sets.

    This is the core of OT factorial typology: the number of distinct
    optimal sets equals the number of language types predicted by the
    constraint set. -/
def factorialOptima {C : Type} [DecidableEq C]
    (candidates : List C)
    (constraints : List (NamedConstraint C))
    (h : candidates ≠ []) : List (List C) :=
  let allRankings := permutations constraints
  let optima := allRankings.map fun ranking =>
    (buildTableau candidates ranking h).optimal
  optima.eraseDups

/-- Number of distinct language types predicted by the factorial typology.
    Equals `|factorialOptima|`. -/
def factorialTypologySize {C : Type} [DecidableEq C]
    (candidates : List C)
    (constraints : List (NamedConstraint C))
    (h : candidates ≠ []) : Nat :=
  (factorialOptima candidates constraints h).length

end Core.OT
