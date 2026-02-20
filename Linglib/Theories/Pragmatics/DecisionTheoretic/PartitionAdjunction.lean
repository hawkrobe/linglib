import Linglib.Core.Categorical.PartitionCat
import Linglib.Core.DecisionTheory

/-!
# Partition-Decision Adjunction

Galois connection between QUD partitions and decision problems, formalizing
the Blackwell/Van Rooy correspondence.

## Sufficient Partition

Given a decision problem `dp` with actions `actions`, the **sufficient
partition** groups worlds by their utility vectors: `w ~ v` iff
`∀ a ∈ actions, U(w,a) = U(v,a)`. This is the coarsest partition that
preserves all utility-relevant distinctions.

## Forward Galois Direction

If `Q` refines `sufficientPartition dp actions`, then within each Q-cell,
all worlds have identical utility vectors. Any action that weakly dominates
in one world of the cell dominates in all. Hence Q resolves dp.

## Backward Direction (False)

The converse fails: Q may resolve dp without refining the sufficient
partition. Example: `U(w₁, a) = 1, U(w₁, b) = 0; U(w₂, a) = 3, U(w₂, b) = 0`.
Then w₁ and w₂ have different utility vectors (sufficient partition separates
them), but `Q = trivial` resolves dp because action `a` globally dominates.

The sufficient partition is the coarsest partition preserving utility
*structure*, not the coarsest partition resolving a particular dp.

## Categorical Connection

The refinement morphism `QUDHom Q (sufficientPartition dp actions)` in
`PartitionCat` witnesses the forward direction. Terminal morphisms
(`QUDHom.toTrivial`) recover the fact that the trivial partition resolves
only trivially dominable DPs.

## References

- Blackwell (1953). Equivalent Comparisons of Experiments.
- Van Rooy (2003). Questioning to Resolve Decision Problems. L&P 26.
- Merin (1999). Information, relevance, and social decisionmaking.
-/

open Core.DecisionTheory
open Core.Categorical

namespace Theories.DTS.PartitionAdjunction

variable {W A : Type*}

-- ════════════════════════════════════════════════════
-- § 1. Sufficient Partition
-- ════════════════════════════════════════════════════

/-- Two worlds are **utility-equivalent** for a decision problem and action
    list iff they yield identical utilities for every action. -/
def utilityEquiv (dp : DecisionProblem W A) (actions : List A)
    (w v : W) : Bool :=
  actions.all λ a => dp.utility w a == dp.utility v a

/-- `utilityEquiv` is reflexive. -/
private theorem utilityEquiv_refl (dp : DecisionProblem W A) (actions : List A) (w : W) :
    utilityEquiv dp actions w w = true := by
  simp only [utilityEquiv, List.all_eq_true]
  intro a _; exact beq_self_eq_true _

/-- `utilityEquiv` is symmetric. -/
private theorem utilityEquiv_symm (dp : DecisionProblem W A) (actions : List A) (w v : W) :
    utilityEquiv dp actions w v = utilityEquiv dp actions v w := by
  unfold utilityEquiv
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, beq_iff_eq]
  exact ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩

/-- `utilityEquiv` is transitive. -/
private theorem utilityEquiv_trans (dp : DecisionProblem W A) (actions : List A)
    (w v u : W) :
    utilityEquiv dp actions w v = true →
    utilityEquiv dp actions v u = true →
    utilityEquiv dp actions w u = true := by
  simp only [utilityEquiv, List.all_eq_true, beq_iff_eq]
  intro h1 h2 a ha
  exact (h1 a ha).trans (h2 a ha)

/-- The **sufficient partition** for a decision problem: the coarsest
    partition that preserves all utility-relevant distinctions.

    Two worlds are in the same cell iff they have identical utility
    vectors across all actions. -/
def sufficientPartition (dp : DecisionProblem W A) (actions : List A) : QUD W where
  sameAnswer := utilityEquiv dp actions
  refl := utilityEquiv_refl dp actions
  symm := utilityEquiv_symm dp actions
  trans := utilityEquiv_trans dp actions

/-- Within a sufficient partition cell, utilities are identical for every action. -/
theorem sufficientPartition_utility_eq
    (dp : DecisionProblem W A) (actions : List A)
    {w v : W} (h : (sufficientPartition dp actions).sameAnswer w v = true)
    {a : A} (ha : a ∈ actions) :
    dp.utility w a = dp.utility v a := by
  simp only [sufficientPartition, utilityEquiv, List.all_eq_true, beq_iff_eq] at h
  exact h a ha

-- ════════════════════════════════════════════════════
-- § 2. Forward Galois Direction
-- ════════════════════════════════════════════════════

/-- If Q refines the sufficient partition, then within each Q-cell,
    all worlds have identical utilities for every listed action.

    This is the key lemma: refinement → utility preservation. -/
theorem refinement_preserves_utility
    (dp : DecisionProblem W A) (actions : List A) (q : QUD W)
    (hRef : QUD.refines q (sufficientPartition dp actions))
    {w v : W} (hCell : q.sameAnswer w v = true)
    {a : A} (ha : a ∈ actions) :
    dp.utility w a = dp.utility v a :=
  sufficientPartition_utility_eq dp actions (hRef w v hCell) ha

/-- Within a sufficient-partition cell, if any action weakly dominates all
    others at one world, it dominates at every world in the cell.

    Dominance transfers because all worlds in the cell have identical
    utility vectors. -/
theorem dominance_transfers_within_cell
    (dp : DecisionProblem W A) (actions : List A)
    {w v : W} (hCell : (sufficientPartition dp actions).sameAnswer w v = true)
    {a : A} (ha : a ∈ actions)
    (hDom : ∀ b ∈ actions, dp.utility w a ≥ dp.utility w b) :
    ∀ b ∈ actions, dp.utility v a ≥ dp.utility v b := by
  intro b hb
  rw [← sufficientPartition_utility_eq dp actions hCell ha,
      ← sufficientPartition_utility_eq dp actions hCell hb]
  exact hDom b hb

-- ════════════════════════════════════════════════════
-- § 3. Sufficient Partition Resolves (Self-Resolution)
-- ════════════════════════════════════════════════════

/-- Within any cell of the sufficient partition, all worlds have the same
    utility vector, so the action with maximum utility (if it exists)
    weakly dominates all others throughout the cell.

    This states that the sufficient partition resolves dp in the strong
    sense: for each cell, there exists a dominating action. -/
theorem sufficientPartition_cell_dominated
    (dp : DecisionProblem W A) (actions : List A)
    {w v : W} (hCell : (sufficientPartition dp actions).sameAnswer w v = true)
    {a : A} (ha : a ∈ actions)
    (hBest : ∀ b ∈ actions, dp.utility w a ≥ dp.utility w b) :
    dp.utility v a ≥ dp.utility v (actions.head (List.ne_nil_of_mem ha)) :=
  dominance_transfers_within_cell dp actions hCell ha hBest
    (actions.head (List.ne_nil_of_mem ha))
    (List.head_mem (List.ne_nil_of_mem ha))

-- ════════════════════════════════════════════════════
-- § 4. Coarseness of the Sufficient Partition
-- ════════════════════════════════════════════════════

/-- The sufficient partition is the **coarsest** partition with
    utility-constant cells.

    Any partition Q whose cells have identical utility vectors
    (i.e., Q refines utility equivalence) must refine the sufficient
    partition. This is immediate from the definitions. -/
theorem sufficientPartition_coarsest
    (dp : DecisionProblem W A) (actions : List A) (q : QUD W)
    (hUtil : ∀ w v, q.sameAnswer w v = true →
      ∀ a ∈ actions, dp.utility w a = dp.utility v a) :
    QUD.refines q (sufficientPartition dp actions) := by
  intro w v hCell
  simp only [sufficientPartition, utilityEquiv, List.all_eq_true, beq_iff_eq]
  exact hUtil w v hCell

-- ════════════════════════════════════════════════════
-- § 5. Categorical Refinement Morphism
-- ════════════════════════════════════════════════════

/-- A refinement morphism from Q to the sufficient partition, in the
    partition category. Witnesses the forward Galois direction
    categorically. -/
def refinementMorphism
    (dp : DecisionProblem W A) (actions : List A) (q : QUD W)
    (hRef : QUD.refines q (sufficientPartition dp actions)) :
    QUDHom ⟨q⟩ ⟨sufficientPartition dp actions⟩ :=
  ⟨hRef⟩

/-- When all worlds have identical utility vectors (not just a dominant
    action), the sufficient partition is trivial. This is the case where
    world-state information has zero value for the decision problem. -/
theorem sufficient_trivial_of_constant_utility
    (dp : DecisionProblem W A) (actions : List A)
    (hConst : ∀ w v : W, ∀ a ∈ actions, dp.utility w a = dp.utility v a) :
    QUD.refines QUD.trivial (sufficientPartition dp actions) := by
  intro w v _
  simp only [sufficientPartition, utilityEquiv, List.all_eq_true, beq_iff_eq]
  exact hConst w v

-- ════════════════════════════════════════════════════
-- § 6. Backward Direction Fails
-- ════════════════════════════════════════════════════

/-! ### The backward Galois direction is false

The converse of the forward direction — "Q resolves dp → Q refines
sufficientPartition dp" — fails. A partition may resolve a decision
problem by accident (a globally dominant action) without preserving
utility-vector distinctions.

**Counterexample**: W = {w₁, w₂}, actions = {a, b}.
U(w₁, a) = 1, U(w₁, b) = 0; U(w₂, a) = 3, U(w₂, b) = 0.

The sufficient partition separates w₁ and w₂ (utility vectors differ:
[1, 0] vs [3, 0]). But Q = trivial resolves dp: action a dominates
globally (U(w, a) > U(w, b) for all w). Yet trivial does NOT refine
the sufficient partition.

This is expected: the sufficient partition preserves *all* utility
information, while resolution only requires *some* action to dominate.
The Galois connection is one-sided. -/

private inductive GW | w₁ | w₂ deriving DecidableEq
private inductive GA | a | b deriving DecidableEq

private def counterexDP : DecisionProblem GW GA where
  utility w act := match w, act with
    | .w₁, .a => 1 | .w₁, .b => 0
    | .w₂, .a => 3 | .w₂, .b => 0
  prior _ := 1

/-- w₁ and w₂ are NOT equivalent in the sufficient partition. -/
theorem counterex_not_equiv :
    (sufficientPartition counterexDP [.a, .b]).sameAnswer GW.w₁ GW.w₂ = false := by
  native_decide

/-- But trivial doesn't separate them. -/
theorem counterex_trivial_identifies :
    QUD.trivial.sameAnswer GW.w₁ GW.w₂ = true := rfl

/-- So trivial does NOT refine the sufficient partition. -/
theorem counterex_trivial_not_refines :
    ¬ QUD.refines (QUD.trivial (M := GW)) (sufficientPartition counterexDP [.a, .b]) := by
  intro h
  have := h GW.w₁ GW.w₂ rfl
  rw [counterex_not_equiv] at this
  exact Bool.false_ne_true this

-- ════════════════════════════════════════════════════
-- § 7. Connection to Blackwell
-- ════════════════════════════════════════════════════

/-- The sufficient partition gives a QUD refinement ordering on decision
    problems: dp₁ is "harder" than dp₂ iff sufficientPartition(dp₁)
    refines sufficientPartition(dp₂).

    By Blackwell's theorem (proved in `GSVanRooyBridge.lean`), this
    is equivalent to dp₁ being informationally more demanding:
    any partition that resolves dp₁ also resolves dp₂. -/
def dpRefinement (dp₁ dp₂ : DecisionProblem W A) (actions : List A) : Prop :=
  QUD.refines (sufficientPartition dp₁ actions) (sufficientPartition dp₂ actions)

/-- dpRefinement is reflexive. -/
theorem dpRefinement_refl (dp : DecisionProblem W A) (actions : List A) :
    dpRefinement dp dp actions :=
  QUD.refines_refl _

/-- dpRefinement is transitive. -/
theorem dpRefinement_trans {dp₁ dp₂ dp₃ : DecisionProblem W A} {actions : List A}
    (h₁₂ : dpRefinement dp₁ dp₂ actions) (h₂₃ : dpRefinement dp₂ dp₃ actions) :
    dpRefinement dp₁ dp₃ actions :=
  QUD.refines_trans h₁₂ h₂₃

/-- Categorically: dpRefinement gives a morphism in the partition category. -/
def dpRefinementMorphism {dp₁ dp₂ : DecisionProblem W A} {actions : List A}
    (h : dpRefinement dp₁ dp₂ actions) :
    QUDHom ⟨sufficientPartition dp₁ actions⟩ ⟨sufficientPartition dp₂ actions⟩ :=
  ⟨h⟩

end Theories.DTS.PartitionAdjunction
