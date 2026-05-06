import Linglib.Theories.Syntax.Minimalist.Merge.Internal

/-!
# No Complexity Loss (NCL) for algebraic Merge
@cite{marcolli-chomsky-berwick-2025} Proposition 1.6.10, book p. 72.

Implements M-C-B Definition 1.6.2 (book p. 64) and Proposition 1.6.10
(book p. 72): a workspace transformation `F → F'` satisfies **No
Complexity Loss** if some component map `Φ₀` from `F` to `F'` is
nondecreasing in `leafCount` (the algebraic analog of MCB's "degree").

Quoting M-C-B (book p. 72): "deg(𝔐(T_i, T_j)) = deg(T_i) + deg(T_j),
which is greater than or equal to both deg(T_i) and deg(T_j). All the
remaining components of the workspace not used by Merge maintain the
same degree. For Internal Merge, similarly, deg(T_v, T/T_v) = deg(T)."

## Contents

- `NCLBetween F F'`: existential form of NCL — there exists a component
  map satisfying the nondecreasing-leafCount condition.
- `em_case1_satisfiesNCL`: the EM Case-1 transformation
  `{S, S'} + F̂ → {.node S S'} + F̂` satisfies NCL via the map
  `S, S' ↦ .node S S'`; each spectator maps to itself.
- `im_satisfiesNCL`: the IM transformation `{T} → {.node Q β}` (where
  Q = T/β via cut c0) satisfies NCL via the constant map; the leafCount
  equality follows from `CutShape.cut_leafCount_conservation` (the Δ^d
  analog of MCB's degree-conservation remark).

## Status

Both EM Case-1 and IM positive directions sorry-free.

## Out of scope

The Sideward NCL negative direction (Sideward 2(b)/3(a)/3(b) FAIL NCL,
hence are excluded by Prop 1.6.10) is not yet formalized. It would need
to refute the existence of *any* component map, not just exhibit one —
strictly harder than the positive direction. Queued behind Sideward
identification work.

## Architectural note

NCL is a *predicate* about Merge transformations, not a Merge operation
itself. It sits at the bottom of the Merge dependency chain (consumes
both External and Internal). When Sideward NCL lands, this file will
import `Sideward.lean` too.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open ConnesKreimer

/-- **M-C-B Definition 1.6.2 (book p. 64), existential form.** A
    workspace transformation `F → F'` satisfies No Complexity Loss if some
    component map `Φ₀ : ∀ T ∈ F, TraceTree α Unit` lands in `F'` and never
    decreases `leafCount`. The Hopf grading `deg(a) = #L(T_a)` is
    `TraceTree.leafCount` (M-C-B identifies these on book p. 64).

    See the section docstring for the relationship to M-C-B's induced
    component map (a strengthening this version doesn't enforce). -/
def NCLBetween {α : Type*} [DecidableEq α]
    (F F' : TraceForest α Unit) : Prop :=
  ∃ (Φ₀ : ∀ T, T ∈ F → TraceTree α Unit),
    (∀ T (h : T ∈ F), Φ₀ T h ∈ F') ∧
    (∀ T (h : T ∈ F), (Φ₀ T h).leafCount ≥ T.leafCount)

/-- **M-C-B Prop 1.6.10, EM Case-1 direction.** The EM workspace equation
    proved by `mergeOp_eps_zero_residual` carries a component map satisfying
    NCL: `S, S' ↦ .node S S'` (degree increases by the other operand's
    positive `leafCount`); each `T ∈ F̂` ↦ itself (degree preserved).

    Quoting M-C-B (book p. 72): "deg(𝔐(T_i, T_j)) = deg(T_i) + deg(T_j),
    which is greater than or equal to both deg(T_i) and deg(T_j). All the
    remaining components of the workspace not used by Merge maintain the
    same degree." -/
theorem em_case1_satisfiesNCL {α : Type*} [DecidableEq α]
    (S S' : TraceTree α Unit) (Fhat : TraceForest α Unit) :
    NCLBetween (({S, S'} : TraceForest α Unit) + Fhat)
               (({.node S S'} : TraceForest α Unit) + Fhat) := by
  refine ⟨fun T _ => if T = S ∨ T = S' then .node S S' else T, ?_, ?_⟩
  -- (a) image is in F'
  · intro T hT
    show (if T = S ∨ T = S' then TraceTree.node S S' else T)
            ∈ ({.node S S'} : TraceForest α Unit) + Fhat
    by_cases hcase : T = S ∨ T = S'
    · rw [if_pos hcase]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    · rw [if_neg hcase]
      have hT_Fhat : T ∈ Fhat := by
        rcases Multiset.mem_add.mp hT with hT_pair | hT_Fhat
        · exfalso; apply hcase
          have h_eq : ({S, S'} : TraceForest α Unit) = S ::ₘ {S'} := rfl
          rw [h_eq, Multiset.mem_cons, Multiset.mem_singleton] at hT_pair
          exact hT_pair
        · exact hT_Fhat
      exact Multiset.mem_add.mpr (Or.inr hT_Fhat)
  -- (b) leafCount nondecreasing
  · intro T _
    show (if T = S ∨ T = S' then TraceTree.node S S' else T).leafCount ≥ T.leafCount
    by_cases hcase : T = S ∨ T = S'
    · rw [if_pos hcase, TraceTree.leafCount_node]
      rcases hcase with rfl | rfl
      · have := TraceTree.leafCount_pos S'; omega
      · have := TraceTree.leafCount_pos S; omega
    · rw [if_neg hcase]

/-- **M-C-B Prop 1.6.10, IM positive direction.** The IM workspace
    transformation `{T} → {.node Q β}` (where Q = T/β is the deletion-
    quotient via the unique cut `c0` extracting β) carries a component map
    satisfying NCL: `T ↦ .node Q β`, with `(.node Q β).leafCount = T.leafCount`
    by leafCount conservation under Δ^d (`cut_leafCount_conservation`,
    the Δ^d analog of M-C-B's degree-conservation remark, book p. 64 —
    paragraph after Def 1.6.2).

    Quoting M-C-B (book p. 72): "For Internal Merge, similarly,
    deg(T_v, T/T_v) = deg(T)."

    The substrate hypotheses match the ones for `mergeOp_im_composition`:
    `c0` is the unique cut with `cutForest = {β}` and `remainderDeletion =
    some Q`.

    Note: no `T ≠ β` hypothesis is required (cf. `mergeOp_im_composition`
    which does require it for non-degeneracy of the algebraic sum). For NCL
    the diagonal case is fine — the component map sends `T ↦ .node Q β`
    with leafCount equality holding regardless. -/
theorem im_satisfiesNCL {α : Type*} [DecidableEq α]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q) :
    NCLBetween (({T} : TraceForest α Unit))
               (({.node Q β} : TraceForest α Unit)) := by
  refine ⟨fun _ _ => .node Q β, ?_, ?_⟩
  -- (a) image (.node Q β) is in {.node Q β}
  · intro _ _
    exact Multiset.mem_singleton.mpr rfl
  -- (b) leafCount nondecreasing: (.node Q β).leafCount ≥ T.leafCount, in fact equal.
  · intro T' hT'
    -- T' ∈ {T}, so T' = T
    rw [Multiset.mem_singleton] at hT'
    subst hT'
    -- Goal: (.node Q β).leafCount ≥ T.leafCount
    rw [TraceTree.leafCount_node]
    -- By cut_leafCount_conservation: c0.cutForest.degForest + deletionLeafCount c0 = T.leafCount
    -- c0.cutForest = {β}, so .degForest = β.leafCount
    -- deletionLeafCount c0 = Q.leafCount (by deletionLeafCount_eq_of_remainderDeletion_some)
    -- Therefore β.leafCount + Q.leafCount = T.leafCount, so .leafCount Q + β.leafCount = T.leafCount ≥ T.leafCount.
    have h_cons := CutShape.cut_leafCount_conservation c0
    rw [h_cf] at h_cons
    rw [TraceForest.degForest_singleton] at h_cons
    rw [CutShape.deletionLeafCount_eq_of_remainderDeletion_some c0 Q h_remainder] at h_cons
    omega


end Minimalist.Merge
