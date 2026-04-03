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
  deriving DecidableEq, Repr

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

/-- The optimal set of a `buildTableau` is non-empty: OT always picks
    at least one winner.

    Proof: all profiles have equal length (= `ranking.length`), so
    `lexLE` is a total preorder on the profile space. By
    `exists_lexLE_minimum`, the non-empty candidate set has a minimum
    element under `lexLE`. That element passes the `optimal` filter. -/
theorem buildTableau_optimal_nonempty {C : Type}
    (candidates : List C) (ranking : List (NamedConstraint C))
    (h : candidates ≠ []) :
    (buildTableau candidates ranking h).optimal ≠ [] := by
  have hlen : ∀ a ∈ candidates, ∀ b ∈ candidates,
      (buildProfile ranking a).length = (buildProfile ranking b).length :=
    fun _ _ _ _ => by simp [buildProfile]
  obtain ⟨m, hm_mem, hm_min⟩ :=
    exists_lexLE_minimum candidates h (buildProfile ranking) hlen
  intro hemp
  have hm_opt : m ∈ (buildTableau candidates ranking h).optimal := by
    simp only [OTTableau.optimal, buildTableau]
    rw [List.mem_filter]
    exact ⟨hm_mem, List.all_eq_true.mpr (fun c hc => hm_min c hc)⟩
  rw [hemp] at hm_opt
  nomatch hm_opt

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
theorem optimal_zero_first {C : Type}
    (candidates : List C) (con : NamedConstraint C)
    (rest : List (NamedConstraint C))
    (h : candidates ≠ [])
    (hExists : ∃ c₀ ∈ candidates, con.eval c₀ = 0)
    : ∀ c ∈ (buildTableau candidates (con :: rest) h).optimal,
        con.eval c = 0 := by
  intro c hc
  simp only [OTTableau.optimal, buildTableau, List.mem_filter, List.all_eq_true] at hc
  obtain ⟨_, hc_all⟩ := hc
  obtain ⟨c₀, hc₀_mem, hc₀_zero⟩ := hExists
  have hle := hc_all c₀ hc₀_mem
  simp only [buildProfile, List.map_cons] at hle
  rw [hc₀_zero] at hle
  rw [lexLE_cons_cons_iff] at hle
  cases hle with
  | inl hlt => exact absurd hlt (Nat.not_lt_zero _)
  | inr heq => exact heq.1

end Core.OT
