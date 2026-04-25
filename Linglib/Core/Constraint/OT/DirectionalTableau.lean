import Linglib.Core.Constraint.OT.Basic
import Linglib.Core.Constraint.OT.EvalMode

/-!
# Directional Tableau — Position-Vector EVAL
@cite{eisner-2000} @cite{eisner-2002} @cite{lamont-2022b}

Sibling to `Core/Constraint/OT/Basic.lean`'s parallel `Tableau`. Where
parallel OT compares candidates by **count** of violations
(`NamedConstraint.eval : C → Nat`), directional OT compares by
**position vector** (`DirectionalConstraint.eval : C → List Nat`,
indicator-coded with positions in left-to-right order). The actual
comparison procedure is governed by an `EvalMode`.

## Why a sibling, not an extension

Per @cite{lamont-2022b}: directional EVAL is theoretically
incompatible with weighted aggregation (Harmonic Grammar, MaxEnt). A
parallel constraint's count can be multiplied by a weight; a position
vector cannot. The existing `NamedConstraint`/`Weighted`/`MaxEnt` stack
is committed to scalar violations and cannot host directional
constraints. So they live in parallel type hierarchies, with
`EvalMode.le_singleton` providing the structural bridge for the
degenerate (singleton-vector) case where the two coincide.

## Scope

This module ships:
- `DirectionalConstraint C` — the constraint type (analog of `NamedConstraint C`)
- `DirectionalTableau C` — the tableau type (analog of `Tableau C n`)
- `DirectionalTableau.optimal` — optimal-set extraction via per-entry
  `EvalMode.le`, lex-aggregated across constraints in ranking order

It deliberately does NOT yet ship:
- A `WeightedDirectional` analog (theoretically incoherent per above)
- A `Stratal × Directional` composition
- An n-step iteration combinator (handled by `Iteration.iterateGen` once
  `HSDerivation` dispatches on `evalMode`; deferred to follow-up)
-/

namespace Core.Constraint.OT

open Core.Constraint.Evaluation

-- ============================================================================
-- § 1: DirectionalConstraint
-- ============================================================================

/-- A directional OT constraint. `eval c` returns the **indicator
    vector** for candidate `c`: positions in left-to-right order,
    with each entry recording the violation status at that position
    (binary `{0, 1}` for the typical case, but `Nat` for gradient).

    The constraint itself is direction-neutral; the *direction* of
    evaluation is supplied by `EvalMode` at the tableau level (per
    @cite{lamont-2022b}'s reframing).

    Distinct from `NamedConstraint C` which has `eval : C → Nat`
    (count). These cannot interconvert without losing position
    information; see `EvalMode.le_singleton` for the degenerate-case
    bridge. -/
structure DirectionalConstraint (C : Type*) where
  name : String := ""
  family : ConstraintFamily
  eval : C → List Nat

-- ============================================================================
-- § 2: Lex Comparison Across Constraints
-- ============================================================================

/-- Lex-compare two profiles (each a `List` of indicator vectors, one
    per constraint in ranking order) under an `EvalMode`. At the first
    constraint position where the two profiles strictly differ under
    `EvalMode.le m`, the better candidate wins. Equal throughout =
    equal-harmony.

    Convention matches the parallel `Tableau` lex order: `LexLEByMode m
    a b` iff `a` is at-least-as-harmonic as `b`. -/
def LexLEByMode (m : EvalMode) :
    List (List Nat) → List (List Nat) → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs =>
    -- a strictly more harmonic than b at this constraint: a wins
    (EvalMode.le m a b ∧ ¬ EvalMode.le m b a) ∨
    -- equal at this constraint: recurse
    (EvalMode.le m a b ∧ EvalMode.le m b a ∧ LexLEByMode m as bs)

instance (m : EvalMode) : ∀ (a b : List (List Nat)), Decidable (LexLEByMode m a b)
  | [], _ => isTrue trivial
  | _ :: _, [] => isFalse fun h => h
  | a :: as, b :: bs =>
    have : Decidable (LexLEByMode m as bs) := instDecidableLexLEByMode m as bs
    inferInstanceAs (Decidable (_ ∨ _))

-- ============================================================================
-- § 3: DirectionalTableau
-- ============================================================================

/-- A tableau where all constraints are `DirectionalConstraint` and
    evaluated under a single `EvalMode`. The mode governs the
    within-constraint comparison; `LexLEByMode` lifts that to the
    across-constraints lex order in ranking position.

    Single-mode (one `evalMode` for all constraints) is the simplest
    case. Mixed-mode rankings — where parallel and directional
    constraints coexist in one ranking — are a future extension and
    require a sum-typed constraint or per-constraint mode field. -/
structure DirectionalTableau (C : Type*) [DecidableEq C] where
  candidates : Finset C
  ranking : List (DirectionalConstraint C)
  evalMode : EvalMode
  nonempty : candidates.Nonempty

namespace DirectionalTableau

variable {C : Type*} [DecidableEq C]

/-- The violation profile of candidate `c`: one indicator vector per
    constraint in `ranking`, in ranking order. -/
def profile (t : DirectionalTableau C) (c : C) : List (List Nat) :=
  t.ranking.map (fun con => con.eval c)

/-- A candidate is **optimal** iff its profile is at-least-as-harmonic
    (under `LexLEByMode t.evalMode`) as every other candidate's. -/
def IsOptimal (t : DirectionalTableau C) (c : C) : Prop :=
  c ∈ t.candidates ∧
  ∀ c' ∈ t.candidates, LexLEByMode t.evalMode (t.profile c) (t.profile c')

instance (t : DirectionalTableau C) (c : C) : Decidable (t.IsOptimal c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The optimal set: all candidates whose profile is at-least-as-harmonic
    as every other candidate's. Computable via `Finset.filter`. -/
def optimal (t : DirectionalTableau C) : Finset C :=
  t.candidates.filter fun c =>
    ∀ c' ∈ t.candidates, LexLEByMode t.evalMode (t.profile c) (t.profile c')

theorem mem_optimal_iff (t : DirectionalTableau C) (c : C) :
    c ∈ t.optimal ↔ t.IsOptimal c := by
  simp only [optimal, Finset.mem_filter, IsOptimal]

end DirectionalTableau

-- ============================================================================
-- § 4: Smoke Test (paper, fig. 3 spirit)
-- ============================================================================

section SmokeTest

/-- Three candidates representing depth-1 results of deleting one
    floating H from `/H₁ H₂ H₃/` (paper, fig. 3 input). Each candidate's
    indicator vector records remaining floating Hs at positions 0, 1, 2
    (left-to-right). -/
inductive DemoCand
  | deletedAt0  -- remaining: positions 1, 2 → indicator [0, 1, 1]
  | deletedAt1  -- remaining: positions 0, 2 → indicator [1, 0, 1]
  | deletedAt2  -- remaining: positions 0, 1 → indicator [1, 1, 0]
  deriving DecidableEq, Repr

/-- *FLOAT for the demo: indicator vector of remaining floating H positions. -/
def demoFloatStar : DirectionalConstraint DemoCand :=
  { name := "*FLOAT"
    family := .markedness
    eval := fun
      | .deletedAt0 => [0, 1, 1]
      | .deletedAt1 => [1, 0, 1]
      | .deletedAt2 => [1, 1, 0] }

/-- DirectionalTableau under *FLOAT^→ (left-to-right). All three
    candidates have the same total *FLOAT count (2 violations each), so
    parallel evaluation would tie. Directional EVAL distinguishes them. -/
def demoTableauLR : DirectionalTableau DemoCand :=
  { candidates := {.deletedAt0, .deletedAt1, .deletedAt2}
    ranking := [demoFloatStar]
    evalMode := .directional .leftToRight
    nonempty := by decide }

/-- DirectionalTableau under *FLOAT^← (right-to-left). The mirror case. -/
def demoTableauRL : DirectionalTableau DemoCand :=
  { demoTableauLR with evalMode := .directional .rightToLeft }

/-- **Smoke test (paper, fig. 3 thesis)**: under directional left-to-right
    EVAL, deleting the leftmost floating H wins — i.e., `.deletedAt0` is
    the unique optimum. This validates that the substrate distinguishes
    candidates that parallel OT cannot (all three have 2 violations on
    *FLOAT). -/
example : demoTableauLR.optimal = {DemoCand.deletedAt0} := by decide

/-- **Mirror smoke test**: under directional right-to-left EVAL,
    deleting the rightmost floating H wins. -/
example : demoTableauRL.optimal = {DemoCand.deletedAt2} := by decide

/-- Bonus: parallel evaluation of the same input would tie all three
    candidates (each has 2 violations on *FLOAT). The substrate
    correctly distinguishes them only because EVAL is directional. -/
example : LexLEByMode .parallel
    [[0, 1, 1]] [[1, 0, 1]] := by decide

example : LexLEByMode .parallel
    [[1, 0, 1]] [[0, 1, 1]] := by decide

end SmokeTest

end Core.Constraint.OT
