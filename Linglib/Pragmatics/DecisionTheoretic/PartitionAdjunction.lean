import Linglib.Semantics.Questions.Partition.Basic
import Linglib.Core.Probability.Decision.Basic
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Partition-Decision Adjunction
[blackwell-1953] [merin-1999-relevance] [van-rooy-2003]

Galois connection between partition questions and decision problems, formalizing the
Blackwell/Van Rooy correspondence.

## Sufficient Partition

Given a decision problem `dp` with actions `actions`, the **sufficient partition** groups
worlds by their utility vectors, the kernel of `w ↦ (U(w, a))_{a ∈ actions}`: `w ~ v` iff
`∀ a ∈ actions, U(w,a) = U(v,a)`. This is the coarsest partition that preserves all
utility-relevant distinctions.

## Forward Galois Direction

If `Q` refines `sufficientPartition dp actions`, then within each Q-cell, all worlds have
identical utility vectors. Any action that weakly dominates in one world of the cell dominates
in all. Hence Q resolves dp.

## Backward Direction (False)

The converse fails: Q may resolve dp without refining the sufficient partition. Example:
`U(w₁, a) = 1, U(w₁, b) = 0; U(w₂, a) = 3, U(w₂, b) = 0`. Then w₁ and w₂ have different
utility vectors (sufficient partition separates them), but `Q = ⊤` resolves dp because action
`a` globally dominates.

The sufficient partition is the coarsest partition preserving utility *structure*, not the
coarsest partition resolving a particular dp.

## Categorical Connection

Partitions ordered by refinement form a preorder, hence a thin category (mathlib's
`Preorder.smallCategory`), and the refinement `Q ≤ sufficientPartition dp actions` is the
morphism `homOfLE` witnessing the forward direction.
-/

open Core.DecisionTheory Core.DecisionTheory.DecisionProblem CategoryTheory

namespace DTS.PartitionAdjunction

variable {W A : Type*}

/-! ### Sufficient partition -/

/-- The **sufficient partition** for a decision problem: two worlds are in the same cell iff
they have identical utility vectors across the listed actions. -/
abbrev sufficientPartition (dp : DecisionProblem ℚ W A) (actions : List A) : Setoid W :=
  Setoid.ker λ w => actions.map (dp.utility w)

theorem sufficientPartition_iff (dp : DecisionProblem ℚ W A) (actions : List A) (w v : W) :
    sufficientPartition dp actions w v ↔ ∀ a ∈ actions, dp.utility w a = dp.utility v a := by
  simp [List.map_inj_left]

/-- Within a sufficient partition cell, utilities are identical for every action. -/
theorem sufficientPartition_utility_eq (dp : DecisionProblem ℚ W A) (actions : List A)
    {w v : W} (h : sufficientPartition dp actions w v) {a : A} (ha : a ∈ actions) :
    dp.utility w a = dp.utility v a :=
  (sufficientPartition_iff dp actions w v).1 h a ha

/-! ### Forward Galois direction -/

/-- If Q refines the sufficient partition, then within each Q-cell, all worlds have identical
utilities for every listed action. -/
theorem refinement_preserves_utility (dp : DecisionProblem ℚ W A) (actions : List A)
    (q : Setoid W) (hRef : q ≤ sufficientPartition dp actions) {w v : W} (hCell : q w v)
    {a : A} (ha : a ∈ actions) :
    dp.utility w a = dp.utility v a :=
  sufficientPartition_utility_eq dp actions (Setoid.le_def.1 hRef hCell) ha

/-- Within a sufficient-partition cell, if any action weakly dominates all others at one
world, it dominates at every world in the cell. -/
theorem dominance_transfers_within_cell (dp : DecisionProblem ℚ W A) (actions : List A)
    {w v : W} (hCell : sufficientPartition dp actions w v) {a : A} (ha : a ∈ actions)
    (hDom : ∀ b ∈ actions, dp.utility w a ≥ dp.utility w b) :
    ∀ b ∈ actions, dp.utility v a ≥ dp.utility v b := by
  intro b hb
  rw [← sufficientPartition_utility_eq dp actions hCell ha,
      ← sufficientPartition_utility_eq dp actions hCell hb]
  exact hDom b hb

/-- The sufficient partition resolves dp in the strong sense: an action of maximum utility at
one world of a cell weakly dominates throughout the cell. -/
theorem sufficientPartition_cell_dominated (dp : DecisionProblem ℚ W A) (actions : List A)
    {w v : W} (hCell : sufficientPartition dp actions w v) {a : A} (ha : a ∈ actions)
    (hBest : ∀ b ∈ actions, dp.utility w a ≥ dp.utility w b) :
    dp.utility v a ≥ dp.utility v (actions.head (List.ne_nil_of_mem ha)) :=
  dominance_transfers_within_cell dp actions hCell ha hBest
    (actions.head (List.ne_nil_of_mem ha))
    (List.head_mem (List.ne_nil_of_mem ha))

/-! ### Coarseness of the sufficient partition -/

/-- The sufficient partition is the coarsest partition with utility-constant cells: any
partition whose cells have identical utility vectors refines it. -/
theorem sufficientPartition_coarsest (dp : DecisionProblem ℚ W A) (actions : List A)
    (q : Setoid W) (hUtil : ∀ w v, q w v → ∀ a ∈ actions, dp.utility w a = dp.utility v a) :
    q ≤ sufficientPartition dp actions :=
  Setoid.le_def.2 λ h => (sufficientPartition_iff dp actions _ _).2 (hUtil _ _ h)

/-- A refinement morphism from Q to the sufficient partition, in the preorder category of
partitions. -/
def refinementMorphism (dp : DecisionProblem ℚ W A) (actions : List A) (q : Setoid W)
    (hRef : q ≤ sufficientPartition dp actions) : q ⟶ sufficientPartition dp actions :=
  homOfLE hRef

/-- When all worlds have identical utility vectors, the sufficient partition is trivial: the
case where world-state information has zero value for the decision problem. -/
theorem sufficient_trivial_of_constant_utility (dp : DecisionProblem ℚ W A) (actions : List A)
    (hConst : ∀ w v : W, ∀ a ∈ actions, dp.utility w a = dp.utility v a) :
    ⊤ ≤ sufficientPartition dp actions :=
  sufficientPartition_coarsest dp actions ⊤ λ w v _ => hConst w v

/-! ### The backward Galois direction is false

A partition may resolve a decision problem by accident (a globally dominant action) without
preserving utility-vector distinctions. With `W = {w₁, w₂}` and actions `{a, b}`, `U(w₁, a) =
1, U(w₁, b) = 0; U(w₂, a) = 3, U(w₂, b) = 0`, the sufficient partition separates w₁ and w₂ but
`⊤` resolves dp, since `a` dominates globally, and `⊤` does not refine the sufficient
partition. -/

private inductive GW | w₁ | w₂ deriving DecidableEq
private inductive GA | a | b deriving DecidableEq

private def counterexDP : DecisionProblem ℚ GW GA where
  utility w act := match w, act with
    | .w₁, .a => 1 | .w₁, .b => 0
    | .w₂, .a => 3 | .w₂, .b => 0
  prior _ := 1

/-- w₁ and w₂ are not equivalent in the sufficient partition. -/
theorem counterex_not_equiv : ¬ sufficientPartition counterexDP [.a, .b] GW.w₁ GW.w₂ := by
  decide

/-- So the trivial partition does not refine the sufficient partition. -/
theorem counterex_trivial_not_refines :
    ¬ (⊤ : Setoid GW) ≤ sufficientPartition counterexDP [.a, .b] :=
  λ h => counterex_not_equiv (Setoid.le_def.1 h trivial)

/-! ### Connection to Blackwell -/

/-- The sufficient partition gives a refinement ordering on decision problems: dp₁ is "harder"
than dp₂ iff sufficientPartition(dp₁) refines sufficientPartition(dp₂). By Blackwell's theorem
(`Core/Probability/Decision/Blackwell.lean`) this is dp₁ being informationally more demanding:
any partition that resolves dp₁ also resolves dp₂. -/
def dpRefinement (dp₁ dp₂ : DecisionProblem ℚ W A) (actions : List A) : Prop :=
  sufficientPartition dp₁ actions ≤ sufficientPartition dp₂ actions

/-- Categorically, `dpRefinement` is a morphism between the sufficient partitions. -/
def dpRefinementMorphism {dp₁ dp₂ : DecisionProblem ℚ W A} {actions : List A}
    (h : dpRefinement dp₁ dp₂ actions) :
    sufficientPartition dp₁ actions ⟶ sufficientPartition dp₂ actions :=
  homOfLE h

end DTS.PartitionAdjunction
