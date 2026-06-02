import Linglib.Syntax.Minimalist.Merge.Internal

/-!
# No Complexity Loss (NCL) for algebraic Merge
[marcolli-chomsky-berwick-2025] Proposition 1.6.10, book p. 72.

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

## InducedMapNCL: MCB Def 1.6.2 verbatim form

`NCLBetween` is the existential form (some map works). MCB Def 1.6.2
demands the **canonical** induced map Φ_0 : π_0(F) → π_0(Φ(F))
satisfies the inequality — Φ_0 is determined by Φ (it sends each
root to the component containing its image).

`InducedMapNCL F F' Φ_0` exposes the induced map as an explicit
parameter rather than existentially quantifying it. This is needed for
the NEGATIVE direction (Sideward 2(b)/3(a)/3(b) violate NCL) — under
the existential form `NCLBetween`, one could falsely satisfy NCL by
choosing a non-canonical map; the strict form forces the canonical map.

## DL: degree-loss function (MCB eq. 1.6.4)

`DL Φ_0 F = min_{a ∈ π_0(F)} (deg(Φ_0(a)) - deg(a))`. NCL ⇔ DL ≥ 0.
Implemented as `DLValue` returning `Int` (so we can express negative
values without ℕ-subtraction issues).

## Sideward NCL negative direction (Prop 1.6.10 negative)

`sideward_2b_violatesInducedMapNCL`, `sideward_3a_violatesInducedMapNCL`,
`sideward_3b_violatesInducedMapNCL`: under the canonical induced map
that sends each original root to the component containing its image,
Sideward operations fail NCL because the deletion-quotient (T/T_v) has
strictly smaller leafCount than T.

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


/-! ## §2: InducedMapNCL — MCB Def 1.6.2 verbatim with canonical map -/

/-- **MCB Definition 1.6.2 (book p. 64), strict form.** The canonical
    induced map `Φ_0 : π_0(F) → π_0(Φ(F))` is named explicitly. NCL holds
    iff for all components `T ∈ F`, `(Φ_0 T).leafCount ≥ T.leafCount`.

    Compare to `NCLBetween`: that's existential ("some map works"); this
    one fixes the map. `NCLBetween F F' = ∃ Φ_0, InducedMapNCL F F' Φ_0`
    (with image-in-F' constraint).

    Required for the NEGATIVE direction (`sideward_*_violatesInducedMapNCL`):
    a Sideward operation might satisfy `NCLBetween` via some non-canonical
    map, but its CANONICAL map (sending each root to where its image lives)
    fails. -/
def InducedMapNCL {α : Type*} [DecidableEq α]
    (F F' : TraceForest α Unit)
    (Φ_0 : ∀ T, T ∈ F → TraceTree α Unit) : Prop :=
  (∀ T (h : T ∈ F), Φ_0 T h ∈ F') ∧
  (∀ T (h : T ∈ F), (Φ_0 T h).leafCount ≥ T.leafCount)

/-- Strict form ⇒ existential form: from a canonical induced map satisfying
    NCL, the existential `NCLBetween` follows. -/
theorem NCLBetween_of_InducedMapNCL {α : Type*} [DecidableEq α]
    {F F' : TraceForest α Unit}
    {Φ_0 : ∀ T, T ∈ F → TraceTree α Unit}
    (h : InducedMapNCL F F' Φ_0) : NCLBetween F F' :=
  ⟨Φ_0, h.1, h.2⟩

/-- **MCB eq. 1.6.4 — per-component degree-loss function.** Per-component
    leafCount difference. NCL ⇔ all values ≥ 0 (matches `InducedMapNCL.2`).

    `Int` rather than ℕ so that violations show up as negative values
    rather than being clamped to 0 by ℕ-subtraction. -/
def DLPerComponent {α : Type*} [DecidableEq α]
    {F : TraceForest α Unit}
    (Φ_0 : ∀ T, T ∈ F → TraceTree α Unit)
    (T : TraceTree α Unit) (h : T ∈ F) : Int :=
  ((Φ_0 T h).leafCount : Int) - T.leafCount

/-- NCL inequality (eq. 1.6.3) per component restated via `DLPerComponent`. -/
theorem DLPerComponent_nonneg_iff_NCL {α : Type*} [DecidableEq α]
    {F F' : TraceForest α Unit}
    (Φ_0 : ∀ T, T ∈ F → TraceTree α Unit) (h_image : ∀ T (h : T ∈ F), Φ_0 T h ∈ F') :
    InducedMapNCL F F' Φ_0 ↔ ∀ T (h : T ∈ F), DLPerComponent Φ_0 T h ≥ 0 := by
  unfold InducedMapNCL DLPerComponent
  refine ⟨fun ⟨_, h2⟩ T hT => by have := h2 T hT; omega,
          fun h => ⟨h_image, fun T hT => by have := h T hT; omega⟩⟩

/-! ## §3: Sideward NCL negative direction (MCB Prop 1.6.10) -/

/-- **MCB Prop 1.6.10 negative — Sideward 2(b) violates InducedMapNCL.**
    Under the canonical induced map sending each root to the component
    containing its image, Sideward 2(b) {T_i, T_j} → {.node T_i β, T_j/β}
    fails NCL because T_j ↦ T_j/β has strictly smaller leafCount.

    MCB (book p. 72): "the root of the component T is mapped (as in
    Definition 1.6.2) to the root of the component T/T_v in the new
    workspace F', with deg(T/T_v) < deg(T); thus, it violates the No
    Complexity Loss constraint."

    For the canonical map specifically: `Φ_0(T_i) = .node T_i β`,
    `Φ_0(T_j) = T_j/β = T_j_q`. The latter has leafCount strictly less
    than T_j (since β.leafCount ≥ 1 and conservation gives
    T_j.leafCount = β.leafCount + T_j_q.leafCount). -/
theorem sideward_2b_violatesInducedMapNCL {α : Type*} [DecidableEq α]
    (T_i T_j β T_j_q : TraceTree α Unit) (c_j : CutShape T_j)
    (h_cf : c_j.cutForest = ({β} : TraceForest α Unit))
    (h_rd : c_j.remainderDeletion = some T_j_q)
    (h_distinct : T_i ≠ T_j) :
    ¬ InducedMapNCL ({T_i, T_j} : TraceForest α Unit)
                    ({(.node T_i β : TraceTree α Unit), T_j_q} : TraceForest α Unit)
        (fun T _ => if T = T_i then .node T_i β else T_j_q) := by
  intro h_ncl
  have h_T_j_mem : T_j ∈ ({T_i, T_j} : TraceForest α Unit) :=
    Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl)
  have h_ineq := h_ncl.2 T_j h_T_j_mem
  have h_neq : T_j ≠ T_i := fun h => h_distinct h.symm
  simp only [if_neg h_neq] at h_ineq
  have h_cons := CutShape.cut_leafCount_conservation c_j
  rw [h_cf, TraceForest.degForest_singleton] at h_cons
  rw [CutShape.deletionLeafCount_eq_of_remainderDeletion_some c_j T_j_q h_rd] at h_cons
  have h_β_pos := TraceTree.leafCount_pos β
  omega

/-- **MCB Prop 1.6.10 negative — Sideward 3(a) violates InducedMapNCL.**
    Workspace `{T_i} → {.node a b, T_i/(a⊔b)}` for a 2-edge cut on T_i
    extracting both `a` and `b`. Canonical map sends T_i ↦ T_i/(a⊔b)
    (the deletion-quotient component containing T_i's root image). Since
    the quotient has lost both `a` and `b`, its leafCount is strictly
    less than T_i's. -/
theorem sideward_3a_violatesInducedMapNCL {α : Type*} [DecidableEq α]
    (T_i a b T_iq : TraceTree α Unit) (c_i : CutShape T_i)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α Unit))
    (h_rd : c_i.remainderDeletion = some T_iq) :
    ¬ InducedMapNCL ({T_i} : TraceForest α Unit)
                    ({(.node a b : TraceTree α Unit), T_iq} : TraceForest α Unit)
        (fun _ _ => T_iq) := by
  intro h_ncl
  have h_T_i_mem : T_i ∈ ({T_i} : TraceForest α Unit) :=
    Multiset.mem_singleton.mpr rfl
  have h_ineq := h_ncl.2 T_i h_T_i_mem
  simp only at h_ineq
  have h_cons := CutShape.cut_leafCount_conservation c_i
  rw [h_cf] at h_cons
  rw [show ({a, b} : TraceForest α Unit).degForest = a.leafCount + b.leafCount from
      TraceForest.degForest_pair a b] at h_cons
  rw [CutShape.deletionLeafCount_eq_of_remainderDeletion_some c_i T_iq h_rd] at h_cons
  have h_a_pos := TraceTree.leafCount_pos a
  have h_b_pos := TraceTree.leafCount_pos b
  omega

/-- **MCB Prop 1.6.10 negative — Sideward 3(b) violates InducedMapNCL.**
    Workspace `{T_i, T_j} → {.node a b, T_i/a, T_j/b}`. Canonical map
    sends T_i ↦ T_i/a and T_j ↦ T_j/b (each root maps to its
    deletion-quotient component). Both quotients have strictly smaller
    leafCount, so NCL fails. -/
theorem sideward_3b_violatesInducedMapNCL {α : Type*} [DecidableEq α]
    (T_i T_j a b T_iq T_jq : TraceTree α Unit)
    (c_i : CutShape T_i) (h_cf_i : c_i.cutForest = ({a} : TraceForest α Unit))
    (h_rd_i : c_i.remainderDeletion = some T_iq)
    (c_j : CutShape T_j) (_h_cf_j : c_j.cutForest = ({b} : TraceForest α Unit))
    (_h_rd_j : c_j.remainderDeletion = some T_jq)
    (_h_distinct : T_i ≠ T_j) :
    ¬ InducedMapNCL ({T_i, T_j} : TraceForest α Unit)
                    ({(.node a b : TraceTree α Unit), T_iq, T_jq}
                        : TraceForest α Unit)
        (fun T _ => if T = T_i then T_iq else T_jq) := by
  intro h_ncl
  have h_T_i_mem : T_i ∈ ({T_i, T_j} : TraceForest α Unit) :=
    Multiset.mem_cons_self _ _
  have h_ineq := h_ncl.2 T_i h_T_i_mem
  simp only [↓reduceIte] at h_ineq
  have h_cons_i := CutShape.cut_leafCount_conservation c_i
  rw [h_cf_i, TraceForest.degForest_singleton] at h_cons_i
  rw [CutShape.deletionLeafCount_eq_of_remainderDeletion_some c_i T_iq h_rd_i] at h_cons_i
  have h_a_pos := TraceTree.leafCount_pos a
  omega

end Minimalist.Merge
