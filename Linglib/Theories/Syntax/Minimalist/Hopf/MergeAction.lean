import Linglib.Theories.Syntax.Minimalist.Hopf.Merge
import Linglib.Theories.Syntax.Minimalist.Derivation

/-!
# Bridge: Algebraic Merge ↔ Linguistic Merge
@cite{marcolli-chomsky-berwick-2025}

This file connects two views of the Merge operation:

- **Algebraic Merge** (Hopf-side): `Minimalist.Hopf.mergeOp S S' : Hc R α →ₗ[R] Hc R α`
  defined in `Merge.lean` per M-C-B Definition 1.3.4. Acts on workspaces
  (multisets of trees) viewed as elements of the bialgebra `Hc R α`.

- **Linguistic Merge** (`Step.apply`): the concrete tree-manipulation
  operation in `Theories/Syntax/Minimalism/Derivation.lean`. Acts on a
  single `SyntacticObject` and produces another `SyntacticObject`.

Per M-C-B Lemma 1.3.6, the two should agree: when applied to a
singleton workspace `{T}` (with `T : SyntacticObject`), `mergeOp S S'`
yields a singleton workspace `{T'}` where `T' = (Step.apply step T)`
for the corresponding linguistic step.

## Status

External Merge bridges (`mergeOp_emR_matches_Step`,
`mergeOp_emL_matches_Step`) are **proven sorry-free** as of Phase 7a
(commits 0.230.741-0.230.743). The full Lemma 1.4.1 with arbitrary
residual workspace `Fhat` (`mergeOp_pair_residual`) is also **proven
sorry-free** as of Phase 7b-A (commits 0.230.747-0.230.751), under the
`MergeTargetFreeWorkspace S S' Fhat` predicate (bundled at 0.230.753)
that pins the workspace to **Case 1 of §1.4.1** (p. 48): S, S' are
members of the workspace (not duplicated), and no admissible cut on
a spectator component extracts S or S' as a subforest element. The
cut conditions explicitly exclude **Sideward Merge** — Cases 2(b),
3(a), 3(b) of §1.4.1 which M-C-B formalize in Lemmas 1.4.4 (p. 54)
and 1.4.5 (p. 55).

This is a **pre-Minimal-Search shortcut**: M-C-B's own elimination of
Sideward (§1.5, pp. 56-59) uses **cost-based ordering** (ε-weighted
derivation cost in the ε → 0 limit) rather than stipulating disjointness.
The unconditional sum-over-matchings analog (eq. 1.3.11, p. 45) is
queued for Phase 7b-A.2; Phase 7d will derive Case-1 dominance from
the Minimal Search cost ordering, turning `MergeTargetFreeWorkspace`
from a stipulated hypothesis into a derived theorem.

Internal Merge is documented as a composition gap (Phase 7c, see §3).

Both EM bridges specialize a general algebraic result `mergeOp_pair`,
which proves `mergeOp S S' (forestToHc {S, S'}) = forestToHc {.node S S'}`
for any pair `(S, S') : TraceTree α Unit` over any commutative
semiring `R`. The proof factors through:

- `comulDelAlgHom_pair` (substrate): `Δ^d({S, S'}) = Δ^d(S) · Δ^d(S')`.
- `mergePost_basis_tensor` (`Merge.lean`): basis-tensor evaluation of
  `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}` returns `forestToHc {.node S S'} * r` if
  the LEFT channel is `{S, S'}`, else `0`.
- 4 cross-term reductions (inlined as `have` blocks in `mergeOp_pair`):
  expand `Δ^d(S) · Δ^d(S')` into `(prim + sum) · (prim + sum)`, prove
  each cross-category contributes 0 except `prim · prim`. Cross-term
  elimination uses `cutForest_ne_singleton_self` and
  `cutForest_add_ne_insert_pair` from
  `Core/Combinatorics/RootedTree/AdmissibleCut.lean`.

## What changed from the legacy version

The legacy `MergeAction.lean` (deleted in this session) was built on
the older substrate (`Workspace = List SyntacticObject`,
`Hc = MonoidAlgebra ℤ (FreeMonoid SyntacticObject)`, no trace nesting).
Its bridge theorems `step_emR_matches_M_EM`, `step_emL_matches_M_EM`,
`step_im_matches_M_IM` were proved against `M_EM`/`M_IM` operators
defined directly on `Workspace`, NOT through the algebraic
`comulAlgHom`/`comulDelAlgHom` machinery.

The new substrate uses `Multiset` workspaces and `mergeOp` defined as
the actual M-C-B Definition 1.3.4 composition
`⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d`. This makes the bridge to `Step.apply`
mathematically more meaningful but technically more involved (the
proofs need to track terms through the linear-algebraic chain).
-/

namespace Minimalist.Hopf

open scoped TensorProduct
open ConnesKreimer

/-! ## §1: Workspace-level bridge predicates

A "bridge predicate" relates a linguistic `Step` to its algebraic
realization via `mergeOp`.

The `MergeTargetFree` predicate captures M-C-B's "Case 1 only" condition
on the workspace (§1.4.1, p. 48): the spectator components of the workspace
admit no Sideward Merge target for the pair (S, S'). This bundles the
4-clause disjointness hypothesis used by `mergeOp_factor_out_singleton`
and `mergeOp_pair_residual` into a single named predicate, and gives a
parallel slot for the IM bridge (Phase 7c) to add its own variant. -/

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

/-! ## §2: External Merge bridge — the Fhat = ∅ subcase

For `Step.emR item` applied to `current`, the result is
`.node current item`. The algebraic side: `mergeOp current.toHc item.toHc`
applied to the 2-tree workspace `{current.toHc, item.toHc}` produces
`forestToHc {.node current item}`.

**Scope (verified against M-C-B 2025 p. 49):**
This file proves M-C-B Lemma 1.4.1 (External Merge) **specialized to the
case where the workspace `Fhat` of spectator components is empty**. The
full Lemma 1.4.1 statement is:

  𝔐_{T_i, T_j}(F) = 𝔐(T_i, T_j) ⊔ Fhat

for `F = T_i ⊔ T_j ⊔ Fhat` where T_i, T_j match two connected components.
Our `mergeOp_pair` handles `Fhat = ∅` (workspace = exactly `{S, S'}`); the
generalization to nonempty `Fhat` is queued for Phase 7b-A. The full
Lemma 1.3.6 (M-C-B p. 44) is the parent claim covering Cases 1, 2, 3 of
§1.4.1; Cases 2/3 (where S or S' is an *accessible term inside* a
component, not a member) require non-primitive coproduct terms and
trace machinery, which are tied to the IM gap.

**Proof strategy:**

1. Unfold `mergeOp = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d`.
2. Apply `comulDelAlgHom_pair`: `Δ^d({S, S'}) = Δ^d(S) · Δ^d(S')`.
3. Expand each `Δ^d(T) = T ⊗ 1 + ∑_c (cutForest c) ⊗ rChan(c)`.
4. Multiply: 4 cross-categories of terms. `mergePost_basis_tensor`
   evaluates each elementary tensor `forestToHc F ⊗ r` to
   `forestToHc {.node S S'} * r` if `F = {S, S'}`, else `0`.
5. Cross-term elimination via the structural lemmas:
   - `prim_S * prim_{S'}`: `F = {S, S'}` ✓ — contributes the answer.
   - `prim_S * cut_{c'}`: `F = {S} + cutForest c'`. For this to equal
     `{S, S'}`, need `cutForest c' = {S'}` — impossible by
     `cutForest_ne_singleton_self`.
   - `cut_c * prim_{S'}`: symmetric.
   - `cut_c * cut_{c'}`: `F = cutForest c + cutForest c'`. Impossible by
     `cutForest_add_ne_insert_pair` (size argument).

The Minimalism-specific bridges (`mergeOp_emR/L_matches_Step`)
specialize `mergeOp_pair` to `R = ℤ`, `α = LIToken`, with `rfl`
bridging `(.node current item).toH.anon (·) = .node current.toHc item.toHc`. -/

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
    workspace of `.node current item` = `(Step.emR item).apply current`. -/
theorem mergeOp_emR_matches_Step
    (current item : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) current.toHc item.toHc
        (forestToHc ({current.toHc, item.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emR item).apply current).toH.anon (fun _ => ())}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  rfl

/-- **External Merge bridge (left-specifier)** (M-C-B Lemma 1.4.1, p. 49,
    Fhat = ∅ subcase, symmetric pair). `mergeOp item.toHc current.toHc`
    applied to `{item.toHc, current.toHc}` yields `.node item current`. -/
theorem mergeOp_emL_matches_Step
    (item current : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) item.toHc current.toHc
        (forestToHc ({item.toHc, current.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toH.anon (fun _ => ())}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  rfl

/-! ## §2.5: Toward the full Lemma 1.4.1 (residual workspace Fhat)

The factor-out lemma below extends `mergeOp_pair` from `Fhat = ∅` toward the full
Lemma 1.4.1 statement (workspace `{S, S'} ⊔ Fhat`, arbitrary residual `Fhat`). It says:
when `T : TraceTree α Unit` satisfies disjointness from `S, S'` (T ≠ S, T ≠ S',
no cut on T extracts S or S'), `mergeOp S S'` "factors through" multiplication
by `forestToHc {T}`. By induction on `Fhat`'s cardinality, this assembles into the
full Lemma 1.4.1 result (queued as Phase 7b-A.3). -/

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
    (hT : MergeTargetFree S S' T)
    (w : Hc R α) :
    mergeOp (R := R) S S' (forestToHc ({T} : TraceForest α Unit) * w)
      = forestToHc ({T} : TraceForest α Unit) * mergeOp (R := R) S S' w := by
  -- Project the bundled hypothesis into the four clauses.
  obtain ⟨hT_ne_S, hT_ne_S', h_no_S_in_T_cuts, h_no_S'_in_T_cuts⟩ := hT
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
    `Fhat : TraceForest α Unit` such that `MergeTargetFreeWorkspace S S' Fhat`
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
    the ε → 0 limit, NOT via stipulation of disjointness. A future Phase 7d
    will derive (rather than stipulate) Case-1 dominance from a cost-ordering
    argument; for now, the `MergeTargetFreeWorkspace` predicate is the
    well-defined bridge to single-output `Step.emR/emL` semantics. -/
theorem mergeOp_pair_residual {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    {S S' : TraceTree α Unit} {Fhat : TraceForest α Unit}
    (hF : MergeTargetFreeWorkspace S S' Fhat) :
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
    -- The bundled hypothesis decomposes: T satisfies MergeTargetFree, Fhat' satisfies
    -- MergeTargetFreeWorkspace, by the head + of_cons projections.
    have hT : MergeTargetFree S S' T := MergeTargetFreeWorkspace.head hF
    have ih' : mergeOp (R := R) S S' (forestToHc (({S, S'} : TraceForest α Unit) + Fhat'))
              = forestToHc (({.node S S'} : TraceForest α Unit) + Fhat') :=
      ih (MergeTargetFreeWorkspace.of_cons hF)
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
    rw [mergeOp_factor_out_singleton hT]
    -- Goal: forestToHc {T} * mergeOp(forestToHc({S,S'} + Fhat'))
    --     = forestToHc {T} * forestToHc({.node S S'} + Fhat')
    -- Apply ih' via congrArg on multiplication.
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-! ## §2.6: Phase 7d limit theorem (cost-based Sideward elimination)

**Phase 7d.4** (M-C-B §1.5.3 + Prop 1.5.1): the cost-weighted Merge operator
`mergeOp_eps 0` evaluates the EM Case-1 contribution **without** the cut
disjointness clauses. The two no-cut clauses of `MergeTargetFreeWorkspace`
are derived from cost minimization (Sideward weights `ε^d → 0` as `ε → 0`);
only the no-duplicate-component clauses remain as a stipulated hypothesis.

This is the principled M-C-B formulation: Sideward Merge is eliminated by
ε → 0 cost ordering, not by syntactic stipulation. -/

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

/-- **Phase 7d limit theorem (general F̂)**: at ε = 0, the cost-weighted Merge
    operator on workspace `{S, S'} + F̂` produces `forestToHc ({.node S S'} + F̂)`
    under just the **no-duplicate-component** hypothesis (`S, S' ∉ F̂`) — the
    `no_cut_*` clauses of `MergeTargetFreeWorkspace` are derived from cost
    minimization. -/
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

/-- **Corollary: `mergeOp_pair_residual` under the weaker no-duplicate-only
    hypothesis** (the `no_cut_*` clauses of `MergeTargetFreeWorkspace` are
    derivable from cost minimization, per the limit theorem). This shows the
    full `MergeTargetFreeWorkspace` is stronger than necessary for the EM
    Case-1 result; only the `not_mem_*` clauses are essential. -/
theorem mergeOp_pair_residual_from_cost {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    {S S' : TraceTree α Unit} {Fhat : TraceForest α Unit}
    (hS : S ∉ Fhat) (hS' : S' ∉ Fhat) :
    mergeOp_eps (R := R) 0 S S' (forestToHc (({S, S'} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node S S'} : TraceForest α Unit) + Fhat) :=
  mergeOp_eps_zero_residual hS hS'

/-! ## §3: Internal Merge bridge

**Important architectural note (per M-C-B Proposition 1.4.2, p. 50):**
Internal Merge is realized in M-C-B's framework as a **composition of
two External Merge operations**, NOT as a single `mergeOp` call:

  IM(β, T) = M_{T/β, β} ∘ M_{β, 1}

where:
- `M_{β, 1}` is a "virtual" External Merge with the unit, which
  conceptually moves `β` from the right channel to the left channel
  of the coproduct (where it can be grafted).
- `M_{T/β, β}` is the actual External Merge that combines the (now
  available) `β` with the contracted `T/β` (where `β`'s position has
  been replaced by a trace).

This means a faithful Internal Merge bridge cannot be a theorem of the
form `mergeOp _ _ _ = forestToHc {...}` — it would have to compose two
`mergeOp` calls. The previous `True`-stubbed theorem was a structural
lie.

We leave this as a documented gap. The composition formulation is
substantial:
1. Define a `mergeOp_chain : List (DecoratedTree × DecoratedTree) →
   Hc → Hc` operator that sequences `mergeOp` calls.
2. State the IM bridge as `mergeOp_chain [(β, 1), (T/β, β)] {current}
   = forestToHc {(Step.im mover _).apply current}` (modulo trace-id
   naming).
3. Prove via Prop 1.4.2's structural argument.

Deferred to a focused future session.
-/

end Minimalist.Hopf
