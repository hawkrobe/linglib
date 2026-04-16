import Linglib.Core.Logic.ConstraintEvaluation

/-!
# Optimality Theory — Core Vocabulary

OT-specific vocabulary layered on `Core.Logic.ConstraintEvaluation`. Provides
named constraints with a faithfulness/markedness distinction, convenience
constructors for building tableaux from ranked constraint lists, and factorial
typology computation.

## Connection to ConstraintEvaluation

`ConstraintEvaluation` provides the generic engine (`LexLE`, `OTTableau`,
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
  deriving DecidableEq, Repr

/-- A named OT constraint with family classification.
    `eval c` returns the number of violations candidate `c` incurs.

    The `name` field is purely documentary — no evaluation function reads it.
    It defaults to `""` so constraints can be defined without a name when
    the string label adds no information. -/
structure NamedConstraint (C : Type) where
  name : String := ""
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

-- ============================================================================
-- § 5: Profile Length Invariant
-- ============================================================================

/-- All profiles produced by `buildProfile` have the same length
    (= the number of constraints). This is the precondition for
    `lexLE_total`, ensuring OT always determines a winner. -/
theorem buildProfile_length {C : Type}
    (ranking : List (NamedConstraint C)) (c : C) :
    (buildProfile ranking c).length = ranking.length := by
  simp [buildProfile]

-- ============================================================================
-- § 6: Optimal Set is Non-Empty
-- ============================================================================

/-- OT always picks at least one winner: there exists an optimal
    candidate in any `buildTableau`.

    Proof: all profiles have equal length (= `ranking.length`), so
    `LexLE` is a total preorder on the profile space. By
    `exists_lexLE_minimum`, the non-empty candidate set has a minimum
    element under `LexLE`. -/
theorem buildTableau_isOptimal_exists {C : Type}
    (candidates : List C) (ranking : List (NamedConstraint C))
    (h : candidates ≠ []) :
    ∃ c, (buildTableau candidates ranking h).IsOptimal c := by
  have hlen : ∀ a ∈ candidates, ∀ b ∈ candidates,
      (buildProfile ranking a).length = (buildProfile ranking b).length :=
    fun _ _ _ _ => by simp [buildProfile]
  obtain ⟨m, hm_mem, hm_min⟩ :=
    exists_lexLE_minimum candidates h (buildProfile ranking) hlen
  exact ⟨m, hm_mem, hm_min⟩

/-- The computed optimal list is non-empty (derived from
    `buildTableau_isOptimal_exists` via `mem_optimal_iff`). -/
theorem buildTableau_optimal_nonempty {C : Type}
    (candidates : List C) (ranking : List (NamedConstraint C))
    (h : candidates ≠ []) :
    (buildTableau candidates ranking h).optimal ≠ [] := by
  obtain ⟨c, hc⟩ := buildTableau_isOptimal_exists candidates ranking h
  intro hemp
  have := (mem_optimal_iff _ c).mpr hc
  rw [hemp] at this
  nomatch this

-- ============================================================================
-- § 7: Top-Constraint Optimality
-- ============================================================================

/-- If any candidate has 0 violations on the top-ranked constraint,
    then **every** optimal candidate has 0 violations on it.

    This is the structural backbone of constraint dominance: once a
    faithfulness constraint (like MxBM-C) is promoted to the top of
    the ranking, it forces all winners to satisfy it perfectly. Any
    candidate that violates it is lexicographically dominated by the
    zero-violation witness — regardless of lower-ranked constraints.

    Used by `BasemapCorrespondence.dominant_coph_selects_basemap_faithful`
    to derive that dominant cophonologies select basemap-faithful outputs. -/
theorem isOptimal_zero_first {C : Type}
    (candidates : List C) (con : NamedConstraint C)
    (rest : List (NamedConstraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con.eval c₀ = 0)
    : ∀ c, (buildTableau candidates (con :: rest) h).IsOptimal c →
        con.eval c = 0 := by
  intro c ⟨_, hc_all⟩
  obtain ⟨c₀, hc₀_mem, hc₀_zero⟩ := hExists
  have hle := hc_all c₀ hc₀_mem
  simp only [buildTableau, buildProfile, List.map_cons] at hle
  rw [hc₀_zero] at hle
  obtain hlt | ⟨heq, _⟩ := hle
  · exact absurd hlt (Nat.not_lt_zero _)
  · exact heq

/-- `∈ .optimal` version of `isOptimal_zero_first`. -/
theorem optimal_zero_first {C : Type}
    (candidates : List C) (con : NamedConstraint C)
    (rest : List (NamedConstraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con.eval c₀ = 0)
    : ∀ c ∈ (buildTableau candidates (con :: rest) h).optimal,
        con.eval c = 0 :=
  fun c hc => isOptimal_zero_first candidates con rest h hExists c
    ((mem_optimal_iff _ c).mp hc)

end Core.OT
