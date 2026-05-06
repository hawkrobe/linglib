import Linglib.Theories.Syntax.Minimalist.Merge.Basic
import Linglib.Theories.Syntax.Minimalist.Derivation

/-!
# Workspace-level bridge predicates for Algebraic Merge
@cite{marcolli-chomsky-berwick-2025}

A "bridge predicate" relates a linguistic `Step` to its algebraic
realization via `mergeOp`.

The `MergeTargetFree` predicate captures M-C-B's "Case 1 only" condition
on the workspace (§1.4.1, p. 48): the spectator components of the workspace
admit no Sideward Merge target for the pair (S, S'). This bundles the
4-clause disjointness hypothesis used by `mergeOp_factor_out_singleton`
and `mergeOp_pair_residual` (in `Merge.External`) into a single named
predicate, and gives a parallel slot for the IM and Sideward bridges
to add their own variants.

This file is the lowest layer of the MCB Merge bridge — `Workspace`-style
predicates only, no `mergeOp` invocations beyond those already in
`Merge.Basic`. Downstream files (`External`, `Internal`, `Sideward`,
`NoComplexityLoss`) consume these primitives.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open ConnesKreimer

/-- A single tree `T` is "merge-target-free" for the pair `(S, S')`: it
    is not itself `S` or `S'`, and no admissible cut on `T` extracts `S`
    or `S'` as a subforest element. Geometrically, `T` contributes nothing
    to `δ_{S, S'}`'s output via either member-level or accessible-term-level
    matching. Polymorphic in the leaf alphabet `α`. -/
structure MergeTargetFree {α : Type*} [DecidableEq α]
    (S S' T : TraceTree α Unit) : Prop where
  /-- T is not the left merge operand. -/
  ne_left  : T ≠ S
  /-- T is not the right merge operand. -/
  ne_right : T ≠ S'
  /-- No admissible cut on T extracts S as a subforest element. -/
  no_cut_left  : ∀ c : CutShape T, S ∉ CutShape.cutForest c
  /-- No admissible cut on T extracts S' as a subforest element. -/
  no_cut_right : ∀ c : CutShape T, S' ∉ CutShape.cutForest c

/-- A workspace forest `F̂` is "merge-target-free" for `(S, S')`: every
    component of `F̂` satisfies `MergeTargetFree`. Equivalent to:
    `S, S' ∉ F̂` (no member-level matching with components) AND no
    admissible cut on any `T ∈ F̂` extracts `S` or `S'` (no accessible-term
    matching, i.e., no Sideward Merge per §1.4.1 Cases 2(b), 3(a), 3(b)).
    Captures the "Case 1 only" reading of M-C-B Lemma 1.4.1 (p. 49). -/
def MergeTargetFreeWorkspace {α : Type*} [DecidableEq α]
    (S S' : TraceTree α Unit) (F : TraceForest α Unit) : Prop :=
  ∀ T ∈ F, MergeTargetFree S S' T

namespace MergeTargetFreeWorkspace

variable {α : Type*} [DecidableEq α]
  {S S' : TraceTree α Unit} {F : TraceForest α Unit}

/-- Workspace-level: `S` is not a member of `F`. -/
lemma not_mem_left (h : MergeTargetFreeWorkspace S S' F) : S ∉ F := by
  intro hS_mem
  exact (h S hS_mem).ne_left rfl

/-- Workspace-level: `S'` is not a member of `F`. -/
lemma not_mem_right (h : MergeTargetFreeWorkspace S S' F) : S' ∉ F := by
  intro hS'_mem
  exact (h S' hS'_mem).ne_right rfl

/-- Workspace-level: no cut on any component extracts `S`. -/
lemma no_cut_left (h : MergeTargetFreeWorkspace S S' F) :
    ∀ T ∈ F, ∀ c : CutShape T, S ∉ CutShape.cutForest c :=
  fun T hT => (h T hT).no_cut_left

/-- Workspace-level: no cut on any component extracts `S'`. -/
lemma no_cut_right (h : MergeTargetFreeWorkspace S S' F) :
    ∀ T ∈ F, ∀ c : CutShape T, S' ∉ CutShape.cutForest c :=
  fun T hT => (h T hT).no_cut_right

/-- Empty workspace is trivially merge-target-free. -/
lemma empty (S S' : TraceTree α Unit) :
    MergeTargetFreeWorkspace S S' (0 : TraceForest α Unit) := fun _ h => by
  simp at h

/-- Cons preservation: if `T ::ₘ F` is merge-target-free then so is `F`. -/
lemma of_cons {T : TraceTree α Unit}
    (h : MergeTargetFreeWorkspace S S' (T ::ₘ F)) :
    MergeTargetFreeWorkspace S S' F :=
  fun U hU => h U (Multiset.mem_cons_of_mem hU)

/-- Cons head: if `T ::ₘ F` is merge-target-free then `T` is. -/
lemma head {T : TraceTree α Unit}
    (h : MergeTargetFreeWorkspace S S' (T ::ₘ F)) :
    MergeTargetFree S S' T :=
  h T (Multiset.mem_cons_self _ _)

end MergeTargetFreeWorkspace

/-- The singleton workspace containing the embedding of `so` as the
    sole tree. The basis vector `forestToHc {so.toHc}` in `Hc ℤ LIToken`. -/
noncomputable def singletonWorkspace (so : Minimalist.SyntacticObject) :
    Hc ℤ LIToken :=
  forestToHc ({so.toHc} : TraceForest LIToken Unit)

end Minimalist.Merge
