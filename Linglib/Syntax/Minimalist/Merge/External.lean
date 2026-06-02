import Linglib.Syntax.Minimalist.Merge.Basic
import Linglib.Syntax.Minimalist.Derivation
import Linglib.Core.Combinatorics.RootedTree.CutAvoiding

/-!
# External Merge bridge: algebraic ↔ linguistic
[marcolli-chomsky-berwick-2025]

Realizes M-C-B §1.4 Lemma 1.4.1 (External Merge) at the algebraic level
and bridges to linguistic `Step.emR`/`Step.emL`.

## Contents

**§1: Lemma 1.4.1, F̂ = ∅ subcase** (lines ≈ `mergeOp_pair`).
For any pair `(S, S') : TraceTree α Unit`, `mergeOp S S'` applied to
`forestToHc {S, S'}` yields `forestToHc {.node S S'}`. Proof: expand
`Δ^d({S, S'}) = Δ^d(S) · Δ^d(S')` via `comulDelAlgHom_pair`, then evaluate
the 4 cross-categories via `mergePost_basis_tensor`. Only the
`prim × prim` cross-term survives.

The Minimalism-specific bridges (`mergeOp_emR/L_matches_Step`) specialize
to `R = ℤ`, `α = LIToken`, with `rfl` bridging
`(.node current item).toHc = .node current.toHc item.toHc`.

**§2: Full Lemma 1.4.1 with residual workspace F̂** (lines ≈
`mergeOp_factor_out_singleton`, `mergeOp_pair_residual`). Under
`CutAvoidingForest ({S, S'}) Fhat` (Connes-Kreimer "Case 1" condition,
defined in `Core/Combinatorics/RootedTree/CutAvoiding.lean`), Merge factors
through multiplication by spectator components; induction on F̂ assembles
the full Case-1 result.

**§3: Phase 7d limit theorem (cost-based Sideward elimination)** (lines ≈
`mergeOp_eps_zero_*`). At ε = 0, `mergeOp_eps` evaluates the EM Case-1
contribution **without** the cut disjointness clauses — these are derived
from cost minimization (Sideward weights `ε^d → 0` as `ε → 0`). Implements
M-C-B §1.5.3 + Prop 1.5.1.

## Status

All theorems sorry-free as of 0.230.804.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open ConnesKreimer

/-- **Algebraic Merge on a 2-tree workspace** (M-C-B Lemma 1.4.1,
    Fhat = ∅ subcase, p. 49). For any pair `(S, S') : TraceTree α Unit`,
    `mergeOp S S'` applied to the basis vector `forestToHc {S, S'}`
    yields `forestToHc {.node S S'}`.

    The 4 cross-term reductions are inlined as `have` blocks below
    (each consumed exactly once); the substrate-level structural lemmas
    `cutForest_ne_singleton_self` and `cutForest_add_ne_insert_pair` do
    the load-bearing elimination work. -/
theorem mergeOp_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (S S' : TraceTree α Unit) :
    mergeOp (R := R) S S' (forestToHc ({S, S'} : TraceForest α Unit))
      = forestToHc ({.node S S'} : TraceForest α Unit) := by
  -- Step 1: reduce mergeOp to mergePost ∘ comulDelAlgHom, apply to {S, S'}.
  show (mergePost (R := R) (α := α) S S' ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({S, S'} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulDelAlgHom_pair,
      comulTreeDel_eq_prim_add_sum, comulTreeDel_eq_prim_add_sum]
  -- Step 2: distribute and push linearity through the 3-layer chain.
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Step 3: each of the 4 cross-terms reduces (inlined as `have`s).
  -- Term 1 (prim × prim): the only surviving term, contributes the answer.
  have h_pp :
      mergePost (R := R) (α := α) S S'
          ((forestToHc (R := R) ({S} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
            * (forestToHc (R := R) ({S'} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = forestToHc (R := R) ({.node S S'} : TraceForest α Unit) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [show ({S} : TraceForest α Unit) + ({S'} : TraceForest α Unit)
        = ({S, S'} : TraceForest α Unit) from rfl]
    rw [mergePost_basis_tensor, if_pos rfl, mul_one]
  -- Term 2 (prim × sum): zero (cuts on S' can't produce {S'}).
  have h_ps :
      mergePost (R := R) (α := α) S S'
          ((forestToHc (R := R) ({S} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
            * ∑ c' : CutShape S',
                forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                  deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
        = 0 := by
    rw [Finset.mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul,
        mergePost_basis_tensor, if_neg]
    intro h
    apply CutShape.cutForest_ne_singleton_self c'
    have : ({S} : TraceForest α Unit) + CutShape.cutForest c'
          = ({S} : TraceForest α Unit) + ({S'} : TraceForest α Unit) := h
    exact Multiset.add_right_inj.mp this
  -- Term 3 (sum × prim): zero (symmetric).
  have h_sp :
      mergePost (R := R) (α := α) S S'
          ((∑ c : CutShape S,
              forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c))
            * (forestToHc (R := R) ({S'} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 := by
    rw [Finset.sum_mul]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one,
        mergePost_basis_tensor, if_neg]
    intro h
    apply CutShape.cutForest_ne_singleton_self c
    have : ({S, S'} : TraceForest α Unit)
         = ({S} : TraceForest α Unit) + ({S'} : TraceForest α Unit) := rfl
    rw [this] at h
    exact Multiset.add_left_inj.mp h
  -- Term 4 (sum × sum): zero (combined cut-forest can't be {S, S'}).
  have h_ss :
      mergePost (R := R) (α := α) S S'
          ((∑ c : CutShape S,
              forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c))
            * (∑ c' : CutShape S',
                forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                  deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
        = 0 := by
    rw [Fintype.sum_mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add,
        mergePost_basis_tensor, if_neg]
    exact CutShape.cutForest_add_ne_insert_pair c c'
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [add_zero]

/-- **External Merge bridge (right-complement)** (M-C-B Lemma 1.4.1, p. 49,
    Fhat = ∅ subcase). `mergeOp current.toHc item.toHc` applied to the
    2-tree workspace `{current.toHc, item.toHc}` yields the singleton
    workspace of `.node current item` = `(Step.emR item).apply current`.

    The hypothesis `h_coh : (current * item).toHc = .node current.toHc item.toHc`
    is the **externalize-respect property at the merged node**: the
    `Quot.out`-based `toHc` on `(current * item)` happens to factor as
    `.node current.toHc item.toHc`. Per MCB §1.12.3 (book p. 116), this
    is the local-coherence condition that some sections satisfy at specific
    nodes; consumers supply the hypothesis when the section is built to
    respect this merge. -/
theorem mergeOp_emR_matches_Step
    (current item : Minimalist.SyntacticObject)
    (h_coh : (current * item).toHc =
      ConnesKreimer.TraceTree.node current.toHc item.toHc) :
    mergeOp (R := ℤ) current.toHc item.toHc
        (forestToHc ({current.toHc, item.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emR item).apply current).toHc}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  -- Step.emR.apply: (Step.emR item).apply current = current * item
  show forestToHc (R := ℤ) ({.node current.toHc item.toHc} : TraceForest LIToken Unit)
    = forestToHc (R := ℤ) ({(current * item).toHc} : TraceForest LIToken Unit)
  rw [h_coh]

/-- **External Merge bridge (left-specifier)** (M-C-B Lemma 1.4.1, p. 49,
    Fhat = ∅ subcase, symmetric pair). `mergeOp item.toHc current.toHc`
    applied to `{item.toHc, current.toHc}` yields `.node item current`. -/
theorem mergeOp_emL_matches_Step
    (item current : Minimalist.SyntacticObject)
    (h_coh : (item * current).toHc =
      ConnesKreimer.TraceTree.node item.toHc current.toHc) :
    mergeOp (R := ℤ) item.toHc current.toHc
        (forestToHc ({item.toHc, current.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toHc}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  show forestToHc (R := ℤ) ({.node item.toHc current.toHc} : TraceForest LIToken Unit)
    = forestToHc (R := ℤ) ({(item * current).toHc} : TraceForest LIToken Unit)
  rw [h_coh]

/-- **Factor-out lemma**: under disjointness on `T` (T ≠ S, T ≠ S', and no cut
    on T extracts S or S'), `mergeOp S S'` commutes with multiplication by
    `forestToHc {T}` on the workspace:

      mergeOp S S' (forestToHc {T} * w) = forestToHc {T} * mergeOp S S' w.

    Proof: expand `comulDelAlgHom (forestToHc {T} * w) = comulTreeDel T *
    comulDelAlgHom w`. Decompose `comulTreeDel T` into prim + cut sum. The
    prim term and non-empty cuts vanish under disjointness via
    `mergePost_left_mul_eq_zero_of_not_le`. The empty cut contributes
    `(1 ⊗ forestToHc {T}) * comulDelAlgHom w`, which by Hc-commutativity and
    `mergePost_right_one_tmul` evaluates to `forestToHc {T} * mergeOp S S' w`. -/
theorem mergeOp_factor_out_singleton {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    {S S' T : TraceTree α Unit}
    (hT_S : CutAvoiding S T) (hT_S' : CutAvoiding S' T)
    (w : Hc R α) :
    mergeOp (R := R) S S' (forestToHc ({T} : TraceForest α Unit) * w)
      = forestToHc ({T} : TraceForest α Unit) * mergeOp (R := R) S S' w := by
  -- Project the two CutAvoiding hypotheses into their four clauses.
  obtain ⟨hT_ne_S, h_no_S_in_T_cuts⟩ := hT_S
  obtain ⟨hT_ne_S', h_no_S'_in_T_cuts⟩ := hT_S'
  -- Step 1: unfold mergeOp = mergePost ∘ comulDelAlgHom
  show (mergePost (R := R) (α := α) S S' ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc (R := R) ({T} : TraceForest α Unit) * w) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  -- comulDelAlgHom is an alg-hom, so it splits the product.
  rw [map_mul]
  -- comulDelAlgHom(forestToHc {T}) = comulTreeDel T (via single + singleton).
  rw [show comulDelAlgHom (R := R) (α := α)
            (forestToHc (R := R) ({T} : TraceForest α Unit))
          = comulTreeDel (R := R) T from by
        unfold forestToHc
        rw [comulDelAlgHom_apply_single, comulForestDel_singleton]]
  -- Decompose comulTreeDel T = prim + sumCut.
  rw [comulTreeDel_eq_prim_add_sum]
  -- Distribute multiplication.
  rw [add_mul, Finset.sum_mul]
  -- Push linearity through the 3-layer chain.
  simp only [map_add, map_sum]
  -- Now LHS = mergePost(prim_T * cdaH w) + ∑ c, mergePost(cut_c * cdaH w).
  -- Term 1 (prim × cdaH w): vanishes via mergePost_left_mul_eq_zero_of_not_le.
  rw [show mergePost (R := R) (α := α) S S'
        ((forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * comulDelAlgHom w) = 0 from by
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      have hT_mem : T ∈ ({S, S'} : TraceForest α Unit) :=
        Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
      have : T = S ∨ T = S' := by
        rw [show ({S, S'} : TraceForest α Unit) = S ::ₘ ({S'} : TraceForest α Unit) from rfl,
            Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
        exact hT_mem
      rcases this with h | h
      · exact hT_ne_S h
      · exact hT_ne_S' h]
  rw [zero_add]
  -- Term 2 (∑ c, cut_c × cdaH w): only c = empty T contributes nontrivially.
  rw [Finset.sum_eq_single (CutShape.empty T)]
  · -- Empty cut term: (1 ⊗ forestToHc {T}) * cdaH w.
    -- By comm + mergePost_right_one_tmul, gives forestToHc {T} * mergeOp w.
    rw [show CutShape.cutForest (CutShape.empty T)
          = (0 : TraceForest α Unit) from CutShape.cutForest_empty T]
    rw [forestToHc_zero]
    -- deletionRightChannel of remainderDeletion of empty cut = forestToHc {T}.
    rw [show CutShape.remainderDeletion (CutShape.empty T) = some T from
          CutShape.remainderDeletion_empty T]
    show mergePost (R := R) (α := α) S S'
          (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T} : TraceForest α Unit))
            * comulDelAlgHom w)
        = forestToHc (R := R) ({T} : TraceForest α Unit) * _
    -- (1 ⊗ forestToHc {T}) * cdaH w = cdaH w * (1 ⊗ forestToHc {T}) by comm
    rw [mul_comm ((1 : Hc R α) ⊗ₜ[R] _) _]
    rw [mergePost_right_one_tmul]
    -- mergePost(cdaH w) = mergeOp S S' w by definition; commute with forestToHc {T}.
    show _ = forestToHc (R := R) ({T} : TraceForest α Unit) *
              (mergeOp (R := R) S S' w)
    rw [mul_comm]
    rfl
  · -- For c ≠ empty T: cf c ≠ 0 (by cutForest_eq_zero_iff), and S, S' ∉ cf c.
    -- Hence cf c ⊄ {S, S'} (as sub-multiset), so mergePost vanishes.
    intro c _ hc_ne_empty
    apply mergePost_left_mul_eq_zero_of_not_le
    intro h_le
    have hcf_subset : CutShape.cutForest c ⊆ ({S, S'} : TraceForest α Unit) :=
      Multiset.subset_of_le h_le
    have hcf_S : S ∉ CutShape.cutForest c := h_no_S_in_T_cuts c
    have hcf_S' : S' ∉ CutShape.cutForest c := h_no_S'_in_T_cuts c
    -- Every element of cf c is in {S, S'}, but neither S nor S' is in cf c.
    -- So cf c is empty. Contradicts hc_ne_empty (via cutForest_eq_zero_iff).
    have hcf_empty : CutShape.cutForest c = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro x hx_mem
      have : x ∈ ({S, S'} : TraceForest α Unit) := hcf_subset hx_mem
      rw [show ({S, S'} : TraceForest α Unit) = S ::ₘ ({S'} : TraceForest α Unit) from rfl,
          Multiset.mem_cons, Multiset.mem_singleton] at this
      rcases this with h | h
      · subst h; exact hcf_S hx_mem
      · subst h; exact hcf_S' hx_mem
    have : c = CutShape.empty T := (CutShape.cutForest_eq_zero_iff c).mp hcf_empty
    exact hc_ne_empty this
  · -- c ∈ univ.
    intro h
    exact absurd (Finset.mem_univ _) h

/-- **Algebraic Merge with residual workspace** (M-C-B Lemma 1.4.1, p. 49 —
    formalization restricted to **Case 1** of §1.4.1, p. 48). For any pair
    `(S, S') : TraceTree α Unit` and any residual workspace
    `Fhat : TraceForest α Unit` such that `CutAvoidingForest ({S, S'}) Fhat`
    (S, S' ∉ Fhat as components, no cut on any T ∈ Fhat extracts S or S' —
    excludes secondary member-level matchings per eq. (1.3.3) and the
    accessible-terms-inside Sideward cases 2(b), 3(a), 3(b) per Lemmas 1.4.4
    (p. 54) and 1.4.5 (p. 55)), we have

      `mergeOp S S' (forestToHc ({S, S'} + Fhat)) = forestToHc ({.node S S'} + Fhat)`.

    **Why these exact conditions.** M-C-B Remark 1.3.8 (p. 47) clarifies that
    External Merge picks out the *primitive part* of the coproduct (member-level
    matchings only); the cut conditions enforce this restriction at the
    formalization layer by excluding the non-primitive contributions that would
    otherwise survive `δ_{S,S'}`.

    **Pre-Minimal-Search shortcut.** This is the conditional EM result. Without
    the disjointness, `mergeOp` produces the sum-over-matchings of eq. (1.3.11),
    p. 45 — including Sideward contributions. M-C-B's own elimination of
    Sideward (per §1.5, pp. 56-59) is via **Minimal Search cost weighting** in
    the ε → 0 limit, realized in `mergeOp_eps_zero_residual` (below) which
    derives Case-1 dominance from cost minimization without the
    `CutAvoidingForest` hypothesis. The connection between the two formulations
    is `mergeOp_eq_mergeOp_eps_zero_under_avoiding`: under `CutAvoidingForest`
    both operators agree pointwise. -/
theorem mergeOp_pair_residual {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    {S S' : TraceTree α Unit} {Fhat : TraceForest α Unit}
    (hF : CutAvoidingForest ({S, S'} : TraceForest α Unit) Fhat) :
    mergeOp (R := R) S S' (forestToHc (({S, S'} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node S S'} : TraceForest α Unit) + Fhat) := by
  -- Strong induction on Fhat via Multiset.induction.
  induction Fhat using Multiset.induction with
  | empty =>
    -- Base case: Fhat = ∅. forestToHc({S,S'} + 0) = forestToHc {S, S'}.
    rw [add_zero, add_zero]
    exact mergeOp_pair S S'
  | cons T Fhat' ih =>
    -- Inductive case: Fhat = T ::ₘ Fhat'.
    -- Project: T avoids both S and S' (head); Fhat' is still {S, S'}-avoiding (of_cons).
    obtain ⟨hT_S, hT_S'⟩ := CutAvoidingForest.head_pair hF
    have ih' : mergeOp (R := R) S S' (forestToHc (({S, S'} : TraceForest α Unit) + Fhat'))
              = forestToHc (({.node S S'} : TraceForest α Unit) + Fhat') :=
      ih hF.of_cons
    -- forestToHc ({S, S'} + T ::ₘ Fhat') = forestToHc {T} * forestToHc ({S, S'} + Fhat')
    -- (using Multiset commutativity and forestToHc_add).
    have h_lhs_eq : ({S, S'} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit) + (({S, S'} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]
      abel
    have h_rhs_eq : ({.node S S'} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit) + (({.node S S'} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]
      abel
    rw [h_lhs_eq, h_rhs_eq, forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT_S hT_S']
    -- Goal: forestToHc {T} * mergeOp(forestToHc({S,S'} + Fhat'))
    --     = forestToHc {T} * forestToHc({.node S S'} + Fhat')
    -- Apply ih' via congrArg on multiplication.
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'


/-- **Limit theorem (F̂ = ∅ case)**: at ε = 0, the cost-weighted Merge
    operator on the 2-tree workspace `{S, S'}` produces exactly
    `forestToHc {.node S S'}` — Case 1 only. The proof expands the
    weighted coproduct (which at ε = 0 reduces to the primitive part
    `(T ⊗ 1) + (1 ⊗ T)` per `comulTreeDel_eps_zero`) and shows only the
    `prim_S × prim_S'` cross-term contributes via `mergePost_basis_tensor`. -/
theorem mergeOp_eps_zero_pair {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α] (S S' : TraceTree α Unit) :
    mergeOp_eps (R := R) 0 S S' (forestToHc ({S, S'} : TraceForest α Unit))
      = forestToHc ({.node S S'} : TraceForest α Unit) := by
  -- Step 1: reduce mergeOp_eps to mergePost ∘ comulDelAlgHom_eps 0.
  show (mergePost (R := R) (α := α) S S' ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({S, S'} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  -- Step 2: comulDelAlgHom_eps 0 on basis vector = comulForestDel_eps 0.
  show mergePost (R := R) (α := α) S S'
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({S, S'} : TraceForest α Unit) (1 : R))) = _
  rw [comulDelAlgHom_eps_apply_single]
  -- Step 3: comulForestDel_eps 0 on a 2-tree forest = product of singletons.
  show mergePost (R := R) (α := α) S S'
        ((({S, S'} : TraceForest α Unit).map (comulTreeDel_eps (R := R) 0)).prod) = _
  rw [show (({S, S'} : TraceForest α Unit).map (comulTreeDel_eps (R := R) 0)).prod
      = comulTreeDel_eps (R := R) 0 S * comulTreeDel_eps (R := R) 0 S' from
    Multiset.prod_pair _ _]
  -- Step 4: each comulTreeDel_eps 0 = primitive part (T ⊗ 1 + 1 ⊗ T).
  rw [comulTreeDel_eps_zero, comulTreeDel_eps_zero]
  -- Step 5: distribute multiplication into 4 cross-terms.
  rw [add_mul, mul_add, mul_add]
  -- Step 6: push linearity through mergePost.
  simp only [map_add]
  -- Step 7: each cross-term reduces via mergePost_basis_tensor.
  -- Helper: cardinality argument used in terms 2-4 to show LEFT ≠ {S, S'}.
  have h_card_ne : ∀ (k : ℕ), k ≠ 2 →
      ∀ {F : TraceForest α Unit}, F.card = k →
        F ≠ ({S, S'} : TraceForest α Unit) := by
    intros k hk_ne F hF_card hF_eq
    have h2 : F.card = (({S, S'} : TraceForest α Unit)).card := by
      rw [hF_eq]
    have : k = 2 := by
      rw [← hF_card, h2]
      rfl
    exact hk_ne this
  -- Term 1 (prim S × prim S'): the only surviving term.
  rw [show mergePost (R := R) (α := α) S S'
        ((forestToHc (R := R) ({S} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({S'} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = forestToHc (R := R) ({.node S S'} : TraceForest α Unit) from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
      rw [show ({S} : TraceForest α Unit) + ({S'} : TraceForest α Unit)
          = ({S, S'} : TraceForest α Unit) from rfl]
      rw [mergePost_basis_tensor, if_pos rfl, mul_one]]
  -- Term 2 (prim S × empty-cut S'): LEFT = {S}, cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) S S'
        ((forestToHc (R := R) ({S} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({S'} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor,
          if_neg (h_card_ne 1 (by decide) (Multiset.card_singleton S))]]
  -- Term 3 (empty-cut S × prim S'): LEFT = {S'}, cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) S S'
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({S} : TraceForest α Unit))
          * (forestToHc (R := R) ({S'} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor,
          if_neg (h_card_ne 1 (by decide) (Multiset.card_singleton S'))]]
  -- Term 4 (empty-cut S × empty-cut S'): LEFT = ∅ (= forestToHc 0), card 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) S S'
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({S} : TraceForest α Unit))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({S'} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor,
          if_neg (h_card_ne 0 (by decide) Multiset.card_zero)]]
  rw [add_zero, add_zero, add_zero]

/-- **Factor-out for `mergeOp_eps 0`**: at ε = 0, mergeOp factors through
    `forestToHc {T}` multiplication for any `T ≠ S, S'` — without requiring
    the `no_cut_*` clauses on T (which were needed for the unweighted
    `mergeOp_factor_out_singleton`). The cut conditions are derived from
    cost minimization here: at ε = 0, all cuts vanish from `comulTreeDel_eps 0 T`,
    leaving only the primitive part `(T ⊗ 1) + (1 ⊗ T)`. -/
theorem mergeOp_eps_zero_factor_out_singleton {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    {S S' T : TraceTree α Unit}
    (hT_ne_S : T ≠ S) (hT_ne_S' : T ≠ S')
    (w : Hc R α) :
    mergeOp_eps (R := R) 0 S S' (forestToHc ({T} : TraceForest α Unit) * w)
      = forestToHc ({T} : TraceForest α Unit) * mergeOp_eps (R := R) 0 S S' w := by
  -- Step 1: unfold mergeOp_eps = mergePost ∘ comulDelAlgHom_eps 0.
  show (mergePost (R := R) (α := α) S S' ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc (R := R) ({T} : TraceForest α Unit) * w) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  -- Alg hom mult: comulDelAlgHom_eps 0 (forestToHc {T} * w)
  --             = comulDelAlgHom_eps 0 (forestToHc {T}) * comulDelAlgHom_eps 0 w
  rw [map_mul]
  -- comulDelAlgHom_eps 0 (forestToHc {T}) = comulTreeDel_eps 0 T (singleton).
  rw [show comulDelAlgHom_eps (R := R) (α := α) (0 : R)
            (forestToHc (R := R) ({T} : TraceForest α Unit))
          = comulTreeDel_eps (R := R) 0 T from by
        unfold forestToHc
        rw [comulDelAlgHom_eps_apply_single]
        show ((({T} : TraceForest α Unit)).map (comulTreeDel_eps (R := R) 0)).prod = _
        rw [Multiset.map_singleton, Multiset.prod_singleton]]
  -- Decompose comulTreeDel_eps 0 T = primitive part (T ⊗ 1 + 1 ⊗ T).
  rw [comulTreeDel_eps_zero]
  -- Distribute multiplication.
  rw [add_mul]
  simp only [map_add]
  -- Term 1 (T ⊗ 1) * comulDelAlgHom_eps 0 w: vanishes since {T} ⊄ {S, S'}.
  rw [show mergePost (R := R) (α := α) S S'
        ((forestToHc (R := R) ({T} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * comulDelAlgHom_eps (R := R) 0 w) = 0 from by
      apply mergePost_left_mul_eq_zero_of_not_le
      intro h_le
      have hT_mem : T ∈ ({S, S'} : TraceForest α Unit) :=
        Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
      have : T = S ∨ T = S' := by
        rw [show ({S, S'} : TraceForest α Unit) = S ::ₘ ({S'} : TraceForest α Unit) from rfl,
            Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
        exact hT_mem
      rcases this with h | h
      · exact hT_ne_S h
      · exact hT_ne_S' h]
  rw [zero_add]
  -- Term 2 (1 ⊗ T) * comulDelAlgHom_eps 0 w: by Hc comm + right-mult helper.
  show mergePost (R := R) (α := α) S S'
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T} : TraceForest α Unit))
          * comulDelAlgHom_eps (R := R) 0 w)
      = forestToHc (R := R) ({T} : TraceForest α Unit) * _
  rw [mul_comm ((1 : Hc R α) ⊗ₜ[R] _) _,
      mergePost_right_one_tmul]
  -- Goal: mergePost (comulDelAlgHom_eps 0 w) * forestToHc {T}
  --     = forestToHc {T} * (mergePost ∘ comulDelAlgHom_eps 0) w
  -- LHS uses Hc commutativity; RHS uses the def of mergeOp_eps.
  show mergePost (R := R) (α := α) S S'
        (comulDelAlgHom_eps (R := R) 0 w) * _
      = _ * mergeOp_eps (R := R) 0 S S' w
  rw [mul_comm]
  rfl

/-- **Cost-derived EM Case 1 with arbitrary residual F̂.** At ε = 0, the
    cost-weighted Merge operator on workspace `{S, S'} + F̂` produces
    `forestToHc ({.node S S'} + F̂)` under just the **no-duplicate-component**
    hypothesis (`S, S' ∉ F̂`) — the `no_cut_*` clauses of `CutAvoidingForest`
    are derived from cost minimization (Sideward weights ε^d → 0). -/
theorem mergeOp_eps_zero_residual {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    {S S' : TraceTree α Unit} {Fhat : TraceForest α Unit}
    (hS : S ∉ Fhat) (hS' : S' ∉ Fhat) :
    mergeOp_eps (R := R) 0 S S' (forestToHc (({S, S'} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node S S'} : TraceForest α Unit) + Fhat) := by
  -- Induction on Fhat. Parallel to mergeOp_pair_residual but using
  -- mergeOp_eps_zero_factor_out_singleton (no cut hypotheses needed).
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_eps_zero_pair S S'
  | cons T Fhat' ih =>
    -- T ≠ S and T ≠ S' (since S, S' ∉ T ::ₘ Fhat').
    have hT_ne_S : T ≠ S := fun h => hS (h ▸ Multiset.mem_cons_self _ _)
    have hT_ne_S' : T ≠ S' := fun h => hS' (h ▸ Multiset.mem_cons_self _ _)
    -- Apply IH on the smaller workspace.
    have hS_Fhat' : S ∉ Fhat' := fun h => hS (Multiset.mem_cons_of_mem h)
    have hS'_Fhat' : S' ∉ Fhat' := fun h => hS' (Multiset.mem_cons_of_mem h)
    have ih' := ih hS_Fhat' hS'_Fhat'
    -- Multiset rearrangement.
    have h_lhs_eq : ({S, S'} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit) + (({S, S'} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]
      abel
    have h_rhs_eq : ({.node S S'} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit) + (({.node S S'} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]
      abel
    rw [h_lhs_eq, h_rhs_eq, forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_eps_zero_factor_out_singleton hT_ne_S hT_ne_S']
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-- **Connection corollary** (MCB §1.5.3, EM Case 1). Under the
    `CutAvoidingForest` hypothesis, both the unweighted `mergeOp` (proven
    via `mergeOp_pair_residual` with the full Case 1 disjointness) and
    the cost-weighted `mergeOp_eps 0` (proven via `mergeOp_eps_zero_residual`
    with only member disjointness, the rest derived from cost minimization)
    produce the same output `forestToHc ({.node S S'} + Fhat)`.

    The two formulations answer different questions:
    - `mergeOp_pair_residual`: under Case-1 disjointness, what does the
      *unweighted* Merge produce? Answer: only EM's contribution survives
      because no Sideward matchings exist.
    - `mergeOp_eps_zero_residual`: under member disjointness alone, what
      does the *cost-weighted* Merge produce at ε = 0? Answer: only EM's
      contribution survives because Sideward matchings exist but vanish at
      ε = 0.

    This corollary witnesses that the two answers coincide on the EM
    Case-1 input, even though they reach the conclusion via different
    suppression mechanisms. -/
theorem mergeOp_eq_mergeOp_eps_zero_under_avoiding
    {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    {S S' : TraceTree α Unit} {Fhat : TraceForest α Unit}
    (hF : CutAvoidingForest ({S, S'} : TraceForest α Unit) Fhat) :
    mergeOp (R := R) S S' (forestToHc (({S, S'} : TraceForest α Unit) + Fhat))
      = mergeOp_eps (R := R) 0 S S'
          (forestToHc (({S, S'} : TraceForest α Unit) + Fhat)) := by
  obtain ⟨hS, hS'⟩ := hF.not_mem_pair
  rw [mergeOp_pair_residual hF, ← mergeOp_eps_zero_residual hS hS']

/-- **EM cost-survival, ε = 0, right-complement** (MCB Prop 1.5.1 EM
    positive direction, `Step.emR` specialization). At ε = 0, the
    cost-weighted Merge `mergeOp_eps 0 current.toHc item.toHc` applied
    to the workspace `{current.toHc, item.toHc}` produces the singleton
    workspace of `(Step.emR item).apply current` with weight 1. The EM
    analogue of `Internal.mergeOp_eps_zero_im_matches_Step`; together
    they realize MCB Prop 1.5.1's "EM and IM survive at ε = 0" claim
    at the linguistic Step bridge level. -/
theorem mergeOp_eps_zero_emR_matches_Step
    (current item : Minimalist.SyntacticObject)
    (h_coh : (current * item).toHc =
      ConnesKreimer.TraceTree.node current.toHc item.toHc) :
    mergeOp_eps (R := ℤ) 0 current.toHc item.toHc
        (forestToHc ({current.toHc, item.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emR item).apply current).toHc}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_eps_zero_pair]
  show forestToHc (R := ℤ) ({.node current.toHc item.toHc} : TraceForest LIToken Unit)
    = forestToHc (R := ℤ) ({(current * item).toHc} : TraceForest LIToken Unit)
  rw [h_coh]

/-- **EM cost-survival, ε = 0, left-specifier** (MCB Prop 1.5.1 EM positive
    direction, `Step.emL` specialization). Symmetric pair to
    `mergeOp_eps_zero_emR_matches_Step`. -/
theorem mergeOp_eps_zero_emL_matches_Step
    (item current : Minimalist.SyntacticObject)
    (h_coh : (item * current).toHc =
      ConnesKreimer.TraceTree.node item.toHc current.toHc) :
    mergeOp_eps (R := ℤ) 0 item.toHc current.toHc
        (forestToHc ({item.toHc, current.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toHc}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_eps_zero_pair]
  show forestToHc (R := ℤ) ({.node item.toHc current.toHc} : TraceForest LIToken Unit)
    = forestToHc (R := ℤ) ({(item * current).toHc} : TraceForest LIToken Unit)
  rw [h_coh]

/-! ## §4: MCB Prop 1.5.1 chain-level (EM-only)

[marcolli-chomsky-berwick-2025] §1.5 rule 5 (book p. 59) defines a
derivation φ as a sequence of Merge operations and the total cost as the
sum of step costs. Bullet 2 + 3 of Prop 1.5.1 (book p. 60-61) operate at
the chain level: chains containing any Sideward step have weight ε^{c(φ)}
→ 0 in the limit ε → 0.

Linglib's `Derivation` (in `Syntax/Minimalist/Derivation.lean`)
has constructors `Step.emR`, `Step.emL`, `Step.im`. There is no
`Step.sideward` because Sideward is suppressed by Prop 1.5.1; there is
no `Step.wlm` because Wholesale Late Merger derivations were never
attested in Phenomena consumers and MCB §1.7 predicts wlm-outputs are
derivable from EM/IM regardless.

This section provides the **EM-only chain bridge**: a joint linguistic+
algebraic fold that tracks the (SyntacticObject, Hc workspace) pair through
each step. For EM-only chains, the algebraic ε = 0 second component matches
`forestToHc {current SO}.toHc` at every stage. The IM chain extension
requires either adding cut-data annotations to `Step.im` or proving
cut-existence from `SyntacticObject.replace` semantics — deferred.
-/

/-- **Single EM step at the algebraic ε = 0 level**: applies `mergeOp_eps 0`
    to the workspace `{current.toHc, item.toHc}` (or symmetric for emL),
    where `item` is being injected from the lexicon into the workspace.
    Returns the singleton workspace of the merged result.

    `noncomputable` because it depends on `mergeOp_eps`. Returns 0 for IM
    steps (not handled at this chain level — see chain-theorem docstring
    for caveats). -/
noncomputable def stepApplyEM_eps_zero :
    Step → Minimalist.SyntacticObject → Hc ℤ LIToken
  | .emR item, current =>
      mergeOp_eps (R := ℤ) 0 current.toHc item.toHc
        (forestToHc ({current.toHc, item.toHc} : TraceForest LIToken Unit))
  | .emL item, current =>
      mergeOp_eps (R := ℤ) 0 item.toHc current.toHc
        (forestToHc ({item.toHc, current.toHc} : TraceForest LIToken Unit))
  | _, _ => 0  -- IM not handled at this chain level

/-- The per-step externalize-respect coherence requirement, packaged as a
    `Prop`-valued helper for chain-level consumers. For `.emR`/`.emL`, the
    relevant `(_ * _).toHc = .node _ _` factorization; for `.im`, vacuous. -/
def stepCoherence (step : Step) (current : Minimalist.SyntacticObject) : Prop :=
  match step with
  | .emR item => (current * item).toHc =
      ConnesKreimer.TraceTree.node current.toHc item.toHc
  | .emL item => (item * current).toHc =
      ConnesKreimer.TraceTree.node item.toHc current.toHc
  | _ => True

/-- For an EM step (`emR` or `emL`), the algebraic ε = 0 application produces
    the singleton workspace of `step.apply current`. Per-step witness for the
    chain theorem; assembles `mergeOp_eps_zero_emR/emL_matches_Step`. -/
theorem stepApplyEM_eps_zero_match (step : Step) (current : Minimalist.SyntacticObject)
    (h_em : ∀ mover traceId, step ≠ .im mover traceId)
    (h_coh : stepCoherence step current) :
    stepApplyEM_eps_zero step current
      = forestToHc (R := ℤ) ({(step.apply current).toHc} : TraceForest LIToken Unit) := by
  match step with
  | .emR item => exact mergeOp_eps_zero_emR_matches_Step current item h_coh
  | .emL item => exact mergeOp_eps_zero_emL_matches_Step item current h_coh
  | .im mover traceId => exact absurd rfl (h_em mover traceId)

/-- **MCB Prop 1.5.1 chain-level, EM-only derivations** (book §1.5 rule 5,
    p. 59). For an EM-only Step list applied to an initial `SyntacticObject`,
    the joint `(linguistic SO, algebraic ε = 0 workspace)` fold preserves the
    invariant that the workspace equals `forestToHc {(current SO).toHc}` at
    every stage. The fold's final result therefore equals
    `(d.final, forestToHc {d.final.toHc})`.

    This realizes the chain-level reading of Prop 1.5.1's bullet 2 + 3 for
    the EM-only case: every step survives at ε = 0 with weight 1, so the
    entire chain produces the linguistic output's singleton workspace in
    `Hc ℤ LIToken`.

    For mixed EM/IM derivations, the IM-step bridge requires cut-data
    annotations (queued separately). -/
theorem em_only_chain_eps_zero (steps : List Step) (initial : Minimalist.SyntacticObject)
    (h_em_only : ∀ s ∈ steps, ∀ mover traceId, s ≠ .im mover traceId)
    (h_coh_chain : ∀ s ∈ steps, ∀ current : Minimalist.SyntacticObject,
      stepCoherence s current) :
    steps.foldl
        (fun (state : Minimalist.SyntacticObject × Hc ℤ LIToken) step =>
          (step.apply state.1, stepApplyEM_eps_zero step state.1))
        (initial, forestToHc ({initial.toHc} : TraceForest LIToken Unit))
      = (steps.foldl (fun so step => step.apply so) initial,
         forestToHc ({(steps.foldl (fun so step => step.apply so) initial).toHc}
           : TraceForest LIToken Unit)) := by
  induction steps generalizing initial with
  | nil => simp
  | cons step rest ih =>
    have h_step_em : ∀ mover traceId, step ≠ .im mover traceId :=
      h_em_only step List.mem_cons_self
    have h_rest_em : ∀ s ∈ rest, ∀ mover traceId, s ≠ .im mover traceId :=
      fun s hs => h_em_only s (List.mem_cons_of_mem step hs)
    have h_step_coh : stepCoherence step initial :=
      h_coh_chain step List.mem_cons_self initial
    have h_rest_coh : ∀ s ∈ rest, ∀ current : Minimalist.SyntacticObject,
        stepCoherence s current :=
      fun s hs => h_coh_chain s (List.mem_cons_of_mem step hs)
    have h_step_eq : stepApplyEM_eps_zero step initial
                  = forestToHc (R := ℤ)
                      ({(step.apply initial).toHc} : TraceForest LIToken Unit) :=
      stepApplyEM_eps_zero_match step initial h_step_em h_step_coh
    show (rest.foldl _ (step.apply initial, stepApplyEM_eps_zero step initial)) = _
    rw [h_step_eq]
    exact ih (step.apply initial) h_rest_em h_rest_coh

end Minimalist.Merge
