import Linglib.Theories.Syntax.Minimalist.Merge.Basic
import Linglib.Theories.Syntax.Minimalist.Derivation

/-!
# Bridge: Algebraic Merge ↔ Linguistic Merge
@cite{marcolli-chomsky-berwick-2025}

This file connects two views of the Merge operation:

- **Algebraic Merge** (Hopf-side): `Minimalist.Merge.mergeOp S S' : Hc R α →ₗ[R] Hc R α`
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

namespace Minimalist.Merge

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
    workspace of `.node current item` = `(Step.emR item).apply current`.

    Both sides use the new trace-aware `toHc` (Phase 7c.3). For EM, neither
    `current` nor `item` introduces trace markers, so `toHc_node` reduces
    `((Step.emR item).apply current).toHc = .node current.toHc item.toHc`. -/
theorem mergeOp_emR_matches_Step
    (current item : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) current.toHc item.toHc
        (forestToHc ({current.toHc, item.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emR item).apply current).toHc}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  -- Step.emR item current = .node current item; toHc_node gives .node current.toHc item.toHc
  rfl

/-- **External Merge bridge (left-specifier)** (M-C-B Lemma 1.4.1, p. 49,
    Fhat = ∅ subcase, symmetric pair). `mergeOp item.toHc current.toHc`
    applied to `{item.toHc, current.toHc}` yields `.node item current`. -/
theorem mergeOp_emL_matches_Step
    (item current : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) item.toHc current.toHc
        (forestToHc ({item.toHc, current.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toHc}
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

/-! ## §2.7: No Complexity Loss (M-C-B Proposition 1.6.10, book p. 72)

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.6.2 (book p. 64), a
workspace transformation Φ : 𝔉_{SO_0} → 𝔉_{SO_0} satisfies the **No
Complexity Loss** principle if the induced component map Φ_0 (sending each
component a to the new component containing the image of the root vertex
of T_a) has nondecreasing degree, where deg(a) = #L(T_a) — that is, the
**Hopf algebra grading** = `TraceTree.leafCount`.

Prop 1.6.10 (book p. 72): only EM and IM satisfy NCL; Sideward 2(b), 3(a),
3(b), 𝔐_{S,1} all violate it. **In particular, NCL distinguishes IM from
Sideward 2(b)** — Minimal Search alone cannot, because the ε-cost ordering
gives them the same leading order (book Remark 1.6.9, p. 71).

**Status of this section.**
- Substrate: `NCLBetween` predicate, grounded in `TraceForest` and
  `TraceTree.leafCount` (the Hopf-grading basis), faithful to Def 1.6.2 modulo
  the existential weakening below.
- EM Case 1: proven via direct construction of the component map on top of
  `mergeOp_eps_zero_residual` (Phase 7d).
- IM: substrate `mergeOp_im_composition` (Phase 7c.2) + IM-NCL
  `im_satisfiesNCL` (Phase A2, sorry-free). Quotient-leafCount conservation
  proved as `CutShape.cut_leafCount_conservation` (the Δ^d analog of M-C-B's
  degree-conservation remark, book p. 64; the leafCount/#L slice only —
  M-C-B's Lemma 1.6.3 (p. 65) and Prop 1.6.4 (p. 66) cover α and σ which
  are not formalized here). The bridge lemma
  `CutShape.deletionLeafCount_eq_of_remainderDeletion_some` connects the
  structural `deletionLeafCount` to the Option-valued `remainderDeletion`.
- Sideward 2(b), 3(a), 3(b): the cuts that produce each Sideward output
  forest are now identified via §4's `IsSingleEdgeAccessibleCut` and
  `IsTwoEdgeAccessibleCut` predicates, with realization theorems
  `mergeOp_sideward_2b/3a/3b{_pair}` (sorry-free as of 0.230.803). The
  cost-suppression at ε = 0 is in §4.1's `mergeOp_eps_zero_for_sideward_*`
  (sorry-free as of 0.230.804). What remains for §2.7 NCL: the Sideward
  *negative* directions (showing each Sideward case violates NCL) require
  the existential-component-map argument flagged below. The 𝔐_{S,1} case
  is independently sorry'd.

**Existential weakening of Def 1.6.2.** M-C-B's Φ_0 is the **induced** map
from root-vertex tracking; ours is existentially quantified over component
maps. For the EM/IM positive directions the existential is satisfied by the
induced map itself (no information lost). For the Sideward negative
directions the existential is HARDER to refute (must rule out every
component map, not just the induced one); when those theorems are added,
they will need the additional argument that no compensating map exists. -/

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

/-! ## §3: Internal Merge bridge (M-C-B Proposition 1.4.2, book p. 50)

Internal Merge is realized in M-C-B's framework as a **composition of two
operators** — one a Merge, the other a "virtual" auxiliary that only exists
inside the composition:

  IM = M_{T/β, β} ∘ M_{β, 1}

where:
- `M_{β, 1}` (= `mergeOpUnit β`, defined in `Merge/Basic.lean §6`) extracts
  β from the right channel of the coproduct and pulls it to the left,
  yielding the workspace `{β, T/β}` from the singleton `{T}`. NOT a Merge
  in its own right (book p. 52 "virtual particles" caveat).
- `M_{T/β, β}` is the actual External Merge that combines β with T/β,
  yielding the workspace `{.node (T/β) β}`.

Phase 7c.2 lands the algebraic composition theorem at the substrate level
(no SyntacticObject bridge yet — that's 7c.4). The proof factors through
a per-cut reduction lemma for `mergeOpUnit β (forestToHc {T})`:
the result is a sum over admissible cuts c of T whose cut-forest is `{β}`,
each contributing `forestToHc {β} * deletionRightChannel c.remainderDeletion`.

Under a "β is uniquely positioned in T" hypothesis (encoded as a unique
cut c0 with `cutForest c0 = {β}`), the sum collapses to a single
contribution, and the full IM composition reduces to EM Case 1
(`mergeOp_pair_residual` with empty F̂). -/

/-- **Per-cut reduction of `mergeOpUnit β (forestToHc {T})`.** Unfolds the
    operator chain through `comulTreeDel`'s primitive-plus-cut-sum
    decomposition; each cut's contribution is filtered by `mergePostUnit`'s
    `δ_{β, 1}` projection, surviving only when the cut-forest equals `{β}`.

    The primitive `T ⊗ 1` term contributes `forestToHc {β}` if `T = β`,
    else 0. -/
theorem mergeOpUnit_apply_singleton {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R] (β T : TraceTree α Unit) :
    mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit))
      = (if T = β then forestToHc ({β} : TraceForest α Unit) else 0)
        + ∑ c : CutShape T,
            if c.cutForest = ({β} : TraceForest α Unit)
              then forestToHc (R := R) ({β} : TraceForest α Unit)
                * deletionRightChannel (R := R) c.remainderDeletion
              else 0 := by
  -- Step 1: unfold mergeOpUnit and reduce to mergePostUnit (comulTreeDel T).
  show mergePostUnit (R := R) (α := α) β
        (comulDelAlgHom (Finsupp.single ({T} : TraceForest α Unit) (1 : R))) = _
  rw [comulDelAlgHom_apply_single, comulForestDel_singleton,
      comulTreeDel_eq_prim_add_sum]
  -- Step 2: distribute mergePostUnit through the (primitive + sum).
  rw [map_add, map_sum]
  -- Step 3: reduce primitive part via mergePostUnit_basis_tensor.
  rw [mergePostUnit_basis_tensor]
  congr 1
  · -- Primitive part: if {T} = {β} then forestToHc {β} * 1 else 0
    --              ↔ if T = β       then forestToHc {β}     else 0
    by_cases hTβ : T = β
    · rw [if_pos hTβ, if_pos (by rw [hTβ]), mul_one]
    · rw [if_neg hTβ, if_neg (by intro h; exact hTβ (Multiset.singleton_inj.mp h))]
  · -- Cut sum: each cut term reduces via mergePostUnit_basis_tensor.
    apply Finset.sum_congr rfl
    intro c _
    rw [mergePostUnit_basis_tensor]

/-- **Unique-cut specialization of `mergeOpUnit_apply_singleton`.** Under
    the hypotheses that
    1. `T ≠ β` (β is not the whole tree, so the primitive part vanishes), and
    2. `c0` is the *unique* admissible cut on T whose cut-forest is `{β}`,

    the per-cut sum collapses to a single contribution. This is the form used
    by the IM composition theorem: it pulls β out of T and leaves the
    deletion-remainder of c0 on the right channel.

    **Note: uniqueness is a substrate convenience, NOT a M-C-B requirement.**
    M-C-B's Prop 1.4.2 (book p. 50) only requires "β is an accessible term
    of a connected component of F isomorphic to T" — it does NOT stipulate
    uniqueness, and multi-occurrence is genuinely allowed (yielding a sum
    output, structurally parallel to the EM multi-matching issue resolved
    for the F̂-residual case in Phase 7b-A). The unique-cut hypothesis here
    matches the *worked example* on book pp. 52–53 (which happens to have a
    single occurrence) but specializes the proposition. Generalizing to the
    sum-output case is queued. -/
theorem mergeOpUnit_apply_singleton_unique
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit))
      = forestToHc (R := R) ({β} : TraceForest α Unit)
          * deletionRightChannel (R := R) c0.remainderDeletion := by
  rw [mergeOpUnit_apply_singleton]
  rw [if_neg hTβ, zero_add]
  rw [Finset.sum_eq_single c0]
  · rw [if_pos h_cf]
  · intro c _ hc_ne
    rw [if_neg]
    intro h
    exact hc_ne (h_unique c h)
  · intro h
    exact absurd (Finset.mem_univ c0) h

/-- **M-C-B Proposition 1.4.2 (book p. 50): Internal Merge as composition.**

    The two-step composition `mergeOp Q β ∘ mergeOpUnit β` applied to the
    singleton workspace `{T}` produces the merged tree `.node Q β`, where
    `Q = T/β` is identified via the deletion-remainder of the unique cut
    extracting β from T.

    **Hypotheses:**
    - `c0` is the unique admissible cut on T with `cutForest = {β}` (the
      "β is uniquely positioned in T" hypothesis; multi-occurrence case
      defers to a sum-output formulation).
    - `c0.remainderDeletion = some Q` (the cut produces a non-trivial
      remainder; for IM we always have at least the trace-replaced root).
    - `T ≠ β` (β is a proper subtree, not the whole workspace).

    Note: no `β ≠ Q` hypothesis is required — `mergeOp_pair` handles the
    diagonal case `Q = β` correctly (the workspace becomes `{β, β}` and
    the merged tree is `.node β β`).

    Quotient-structure note: under `comulDelAlgHom` (the deletion variant
    Δ^d, which `mergeOp` uses), the deeper copy of β is *removed* from T
    via edge contraction — book p. 53 eq. (1.4.2) shows `T₁ = T/^d T₂`
    with `{the, apple}` struck through, not replaced by a trace. Trace
    replacement is the Δ^c story (book p. 53 bottom). So the algebraic
    quotient `Q = T/β` here has β's leaves removed entirely, which makes
    `β ≠ Q` typical but not enforced by the substrate. The Step.im
    bridge (Phase 7c.4) reconciles this with the linguistic-layer
    `mkTrace` sentinel via a trace-aware `SyntacticObject.toHc`
    projection.

    The proof is two steps:
    1. Apply `mergeOpUnit_apply_singleton_unique` to reduce the inner
       `mergeOpUnit β (forestToHc {T})` to `forestToHc {β, Q}`.
    2. Apply EM Case 1 (`mergeOp_eps_zero_pair` after collapsing to the
       unweighted form via `mergeOp_eps_one`) to merge `Q` and `β` into
       `.node Q β`.

    **Caveat (book p. 52):** This composition is the algebraic realization
    of IM, but `mergeOpUnit` (= `M_{β, 1}`) is NOT itself a Merge operation —
    it only exists as the first half of this composition, like virtual
    particles in physics. -/
theorem mergeOp_im_composition
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q)
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOp (R := R) Q β
        (mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit)))
      = forestToHc (R := R) ({.node Q β} : TraceForest α Unit) := by
  -- Step 1: mergeOpUnit β (forestToHc {T}) = forestToHc {β} * forestToHc {Q}
  --                                        = forestToHc ({β} + {Q})
  --                                        = forestToHc {β, Q}
  rw [mergeOpUnit_apply_singleton_unique β T c0 h_cf h_unique hTβ,
      h_remainder]
  -- Now: mergeOp Q β (forestToHc {β} * deletionRightChannel (some Q)) = ...
  -- deletionRightChannel (some Q) = forestToHc {Q}.
  show mergeOp (R := R) Q β
        (forestToHc ({β} : TraceForest α Unit) *
         forestToHc ({Q} : TraceForest α Unit)) = _
  rw [← forestToHc_add]
  -- Goal: mergeOp Q β (forestToHc ({β} + {Q})) = forestToHc {.node Q β}
  -- Rewrite {β} + {Q} = {Q, β} (multiset).
  -- Multiset add commutes; {Q, β} = {Q} + {β} = {β} + {Q} definitionally.
  have h_swap : ({β} : TraceForest α Unit) + ({Q} : TraceForest α Unit)
              = ({Q, β} : TraceForest α Unit) :=
    add_comm _ _
  rw [h_swap]
  -- Now apply EM Case 1: mergeOp Q β (forestToHc {Q, β}) = forestToHc {.node Q β}
  -- Use mergeOp_eps_zero_pair (which is for ε = 0) and mergeOp_eps_one to bridge.
  -- Actually the cleanest is to use mergeOp_pair directly. Let me check what's available.
  -- Since mergeOp = mergeOp_eps 1, we use mergeOp_pair (the ε=1 EM Case 1 theorem).
  exact mergeOp_pair Q β

/-- **Step.im argument-order variant of `mergeOp_im_composition`.**

    `Step.im mover traceId current = .node mover (current.replace mover (mkTrace traceId))`
    has mover LEFT, traced (= the algebraic Q) RIGHT. M-C-B's `M_{T/β, β}`
    has Q LEFT, β RIGHT (the convention `mergeOp_im_composition` follows).

    This swap-variant produces `forestToHc {.node β Q}` instead of
    `{.node Q β}`, matching `Step.im`'s constructor order. The proof is
    structurally simpler than the swap-needing version:
    `{β} + {Q} = {β, Q}` definitionally (no `add_comm` needed). -/
theorem mergeOp_im_composition_moverLeft
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q)
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOp (R := R) β Q
        (mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit)))
      = forestToHc (R := R) ({.node β Q} : TraceForest α Unit) := by
  rw [mergeOpUnit_apply_singleton_unique β T c0 h_cf h_unique hTβ, h_remainder]
  show mergeOp (R := R) β Q
        (forestToHc ({β} : TraceForest α Unit) *
         forestToHc ({Q} : TraceForest α Unit)) = _
  rw [← forestToHc_add]
  -- {β} + {Q} = {β, Q} definitionally (no swap needed for mover-LEFT order)
  show mergeOp (R := R) β Q
        (forestToHc ({β, Q} : TraceForest α Unit)) = _
  exact mergeOp_pair β Q

/-! ## §3.2: Step.im bridge (Phase 7c.4)

`Step.im mover traceId current` produces `.node mover (current.replace mover
(mkTrace traceId))` at the linguistic surface. The trace-aware `toHc`
(Phase 7c.3) maps `mkTrace`-leaves to algebraic `.trace ()` constructors.

The bridge below states that `mergeOp mover.toHc Q ∘ mergeOpUnit mover.toHc`
applied to the singleton workspace `{current.toHc}` produces the same
TraceTree as `(Step.im mover traceId).apply current` projected via `toHc`.

**Hypotheses required (substrate-level):** `c0` is the unique cut on
`current.toHc` extracting `mover.toHc`, with deletion-remainder
`(current.replace mover (mkTrace traceId)).toHc`. Auto-deriving these
hypotheses from the `Step.im` structure (i.e., showing that there IS a
canonical cut on `current.toHc` for any `mover` accessible in `current`,
and its deletion-remainder is the trace-replaced quotient) is non-trivial
substrate work and is **deferred** — these would be standalone substrate
lemmas relating `SyntacticObject.replace` to `CutShape.remainderDeletion`. -/

/-- **Step.im algebraic bridge (M-C-B Prop 1.4.2 specialization).**

    Given the cut data `c0` linking the algebraic deletion-quotient on
    `current.toHc` to the trace-replaced linguistic quotient
    `(current.replace mover (mkTrace traceId)).toHc`, the IM composition
    `mergeOp mover.toHc Q ∘ mergeOpUnit mover.toHc` reproduces
    `((Step.im mover traceId).apply current).toHc`.

    Closes the IM gap in the algebraic-↔-linguistic Merge bridge,
    completing Phase 7c. -/
theorem mergeOp_im_matches_Step
    (current mover : Minimalist.SyntacticObject) (traceId : Nat)
    (c0 : CutShape current.toHc)
    (h_cf : c0.cutForest = ({mover.toHc} : TraceForest LIToken Unit))
    (h_remainder : c0.remainderDeletion =
      some (current.replace mover (Minimalist.mkTrace traceId)).toHc)
    (h_unique : ∀ c : CutShape current.toHc,
      c.cutForest = ({mover.toHc} : TraceForest LIToken Unit) → c = c0)
    (h_curr_ne_mover : current.toHc ≠ mover.toHc) :
    mergeOp (R := ℤ) mover.toHc
        (current.replace mover (Minimalist.mkTrace traceId)).toHc
        (mergeOpUnit (R := ℤ) mover.toHc
          (forestToHc ({current.toHc} : TraceForest LIToken Unit)))
      = forestToHc (R := ℤ)
          ({((Step.im mover traceId).apply current).toHc}
            : TraceForest LIToken Unit) := by
  -- Apply the mover-LEFT IM composition with β = mover.toHc, T = current.toHc,
  -- Q = (current.replace mover (mkTrace traceId)).toHc.
  rw [mergeOp_im_composition_moverLeft mover.toHc current.toHc
        (current.replace mover (Minimalist.mkTrace traceId)).toHc
        c0 h_cf h_remainder h_unique h_curr_ne_mover]
  -- Result: forestToHc {.node mover.toHc (current.replace mover (mkTrace _)).toHc}
  -- Need: forestToHc {((Step.im mover traceId).apply current).toHc}
  -- Step.im mover traceId current = .node mover (current.replace mover (mkTrace traceId))
  -- toHc_node: (.node a b).toHc = .node a.toHc b.toHc
  rfl

/-! ## §4: Sideward Merge realization (M-C-B Lemmas 1.4.4 + 1.4.5, book pp. 54-55)

**Verbatim from MCB §1.4.5 (Sideward Merge, Cases 2(b) and 3(b), p. 54):**

> Case 2(b) corresponds to a case of Sideward Merge. Here, one obtains in
> the new workspace F' a component of the form M(T_i, β) and a component
> of the form T_j/β. Similarly, case 3(b) also represents a case of Sideward
> Merge, where in the resulting workspace F', one has new components: M(α, β),
> as well as T_i/α and T_j/β.

**Lemma 1.4.4** (MCB p. 54): The two cases of Sideward Merge 2(b) and 3(b)
are realized by the Merge operators of (1.3.7) with M_{T_i, β} (with T_i
occurring as a component of F and β as an accessible term of a different
component T_j of F), and M_{α, β} (with α ∈ Acc(T_i) and β ∈ Acc(T_j), for
two components i ≠ j of F).

> Proof. In the Sideward Merge 2(b) the operator δ_{T_i, β} picks the term
> of the coproduct Δ(F), for F = ⊔_a T_a, of the form
>   (T_i ⊔ β) ⊗ (T_j/β ⊔ F̂),
> with F̂ = ⊔_{a≠i,j} T_a. Then ℬ⊗id acts on this term, producing
>   M(T_i, β) ⊗ (T_j/β ⊔ F̂),
> and applying the product ⊔ to this, we obtain
>   M(T_i, β) ⊔ T_j/β ⊔ F̂
> as expected. Case 3(b) of the Sideward Merge is analogous, with δ_{α, β}
> selecting (α ⊔ β) ⊗ (T_i/α ⊔ T_j/β ⊔ F̂), which is mapped to
> M(α, β) ⊔ T_i/α ⊔ T_j/β ⊔ F̂ as expected.

**Verbatim from MCB §1.4.6 (Sideward Merge, Case 3(a), p. 54-55):**

Case 3(a) is also called "Countercyclic Merge". The new workspace F' contains
a new component M(α, β) and a modified component T_i/(α, β), where
T_i/(α, β) writes for the cancellation from the accessible terms of the
deeper copies of α and β inside T_i (also written T_i/(α ⊔ β)).

**Lemma 1.4.5** (MCB p. 55): Case 3(a) of Merge is realized as M_{α, β},
where matching terms in F = ⊔_i T_i are found as disjoint accessible terms
α ≃ T_v, β ≃ T_w of the same component T_a of the workspace, corresponding
to an admissible cut on two edges, and to a term of the coproduct of the form
   T_v ⊔ T_w ⊗ (T_a/(T_v ⊔ T_w) ⊔ F̂),
with F̂ = ⊔_{i≠a} T_i.

> Proof. δ_{α, β} selects T_v ⊔ T_w ⊗ (T/(T_v ⊔ T_w) ⊔ F̂) in the
> coproduct, with α ≃ T_v, β ≃ T_w, which ℬ⊗id then maps to
> M(T_v, T_w) ⊗ T/(T_v ⊔ T_w) ⊔ F̂ and ⊔ maps to
> M(T_v, T_w) ⊔ T/(T_v ⊔ T_w) ⊔ F̂.

## Status of this section

**Sorry-free as of 0.230.804.** The realization lemmas (Lemma 1.4.4 + 1.4.5)
are proven for both the F̂ = ∅ subcase (`*_pair`) and the residual F̂ ≠ ∅
generalisation (bare name) — the residuals reuse `mergeOp_factor_out_singleton`
via Multiset induction, parametric in (S, S'). The cost-suppression
theorems (§4.1) are proven via `comulTreeDel_eps_zero` collapsing the
ε-weighted coproduct to its primitive part at ε = 0; no Phase 7d
machinery (residual factor-out) is used since the suppression argument
is a coproduct-degeneration, not a workspace-induction.

**Cut identification.** The cuts producing Sideward outputs are named
by the `IsSingleEdgeAccessibleCut T_j β c_β` (cf c_β = {β}) and
`IsTwoEdgeAccessibleCut T_i α_t β c` (cf c = {α_t, β}) predicates
defined below. These pick out the surviving cross-term in the
(prim + sum) × (prim + sum) expansion of `comulDelAlgHom`.

**Scope tightening (vs. MCB Lemma 1.4.4 / 1.4.5 in their full form).**
The realization theorems all carry uniqueness hypotheses (`h_unique`,
`h_unique_α`, `h_unique_β`) requiring there be a **unique** cut producing
the given subforest. MCB's lemmas implicitly sum over all matching cuts
(eq. (1.3.3)); the unique-witness restriction is a real scope tightening,
appropriate for the analyst-supplied case where the derivation has a
canonical extraction. The general multi-witness sum case is queued.
-/

/-- A `CutShape c_β : CutShape T_j` **identifies an accessible term β** when
    its forest is the singleton `{β}` — i.e., the cut extracts exactly β
    from T_j as a subforest. This is the substrate predicate corresponding
    to "β ∈ Acc(T_j)" in MCB §1.4.1, witnessed at the algebraic level by
    the existence of an admissible cut producing β. -/
def IsSingleEdgeAccessibleCut {α : Type*} [DecidableEq α]
    (T_j β : TraceTree α Unit) (c_β : CutShape T_j) : Prop :=
  CutShape.cutForest c_β = ({β} : TraceForest α Unit)

instance {α : Type*} [DecidableEq α]
    (T_j β : TraceTree α Unit) (c_β : CutShape T_j) :
    Decidable (IsSingleEdgeAccessibleCut T_j β c_β) := by
  unfold IsSingleEdgeAccessibleCut; infer_instance

/-- **Sideward Merge case 2(b) realization, F̂ = ∅ subcase** (M-C-B Lemma
    1.4.4, p. 54). The 2-tree-workspace base case: `mergeOp T_i β` on
    `{T_i, T_j}` (with β an admissible-cut-extracted accessible term of T_j)
    produces `{M(T_i, β), T_j/β}`.

    Proof structure parallel to `mergeOp_pair` (§2): expand the coproduct
    as (prim + sum) × (prim + sum) for the two components T_i, T_j; show
    only the **prim_{T_i} × cut_{c_β}** cross-term survives. The other
    three cross-terms vanish by the disjointness hypotheses. -/
theorem mergeOp_sideward_2b_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j β T_j_q : TraceTree α Unit)
    (c_β : CutShape T_j)
    (h_cut : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique : ∀ c : CutShape T_j, c ≠ c_β →
                CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_T_i : ∀ c : CutShape T_j, T_i ∉ CutShape.cutForest c)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp (R := R) T_i β
        (forestToHc ({T_i, T_j} : TraceForest α Unit))
      = forestToHc ({.node T_i β, T_j_q} : TraceForest α Unit) := by
  -- Step 1: reduce mergeOp to mergePost ∘ comulDelAlgHom.
  show (mergePost (R := R) (α := α) T_i β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulDelAlgHom_pair,
      comulTreeDel_eq_prim_add_sum, comulTreeDel_eq_prim_add_sum]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim_{T_i} × prim_{T_j}): F = {T_i, T_j} ≠ {T_i, β} since β ≠ T_j.
  have h_pp : mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- {T_i, T_j} = {T_i, β} ⟹ T_j = β by left-cancellation on multisets.
    apply h_β_ne_Tj
    have h1 : ({T_i, T_j} : TraceForest α Unit)
            = ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit) := rfl
    have h2 : ({T_i, β} : TraceForest α Unit)
            = ({T_i} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
    rw [h1, h2] at h_eq
    have h_singletons := Multiset.add_right_inj.mp h_eq
    exact (Multiset.singleton_inj.mp h_singletons).symm
  -- Term 2 (prim_{T_i} × cut sum): only c' = c_β survives, contributes the answer.
  have h_ps : mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = forestToHc (R := R) ({.node T_i β, T_j_q} : TraceForest α Unit) := by
    rw [Finset.mul_sum]
    simp only [map_sum]
    rw [Finset.sum_eq_single c_β]
    · -- c' = c_β: surviving term.
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul]
      rw [show ({T_i} : TraceForest α Unit) + CutShape.cutForest c_β
            = ({T_i, β} : TraceForest α Unit) from by
          rw [show CutShape.cutForest c_β = ({β} : TraceForest α Unit) from h_cut]
          rfl]
      rw [mergePost_basis_tensor, if_pos rfl, h_remainder]
      show forestToHc (R := R) ({.node T_i β} : TraceForest α Unit) *
            forestToHc (R := R) ({T_j_q} : TraceForest α Unit) = _
      rw [← forestToHc_add]; rfl
    · -- c' ≠ c_β: cf(c') ≠ {β}, so {T_i} + cf(c') ≠ {T_i, β}.
      intro c' _ hc'
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      apply h_unique c' hc'
      have h_target : ({T_i, β} : TraceForest α Unit)
                    = ({T_i} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
      rw [h_target] at h_eq
      exact Multiset.add_right_inj.mp h_eq
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Term 3 (cut sum × prim_{T_j}): cf(c) + {T_j} = {T_i, β} forces T_j ∈ {T_i, β}.
  have h_sp : mergePost (R := R) (α := α) T_i β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Finset.sum_mul]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- T_j ∈ LHS = cf(c) + {T_j}; under h_eq, T_j ∈ {T_i, β}.
    have h_T_j_mem : T_j ∈ CutShape.cutForest c + ({T_j} : TraceForest α Unit) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_j_mem
    rw [show ({T_i, β} : TraceForest α Unit) = T_i ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_distinct h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (sum × sum): cf(c) + cf(c') = {T_i, β} forces both to be empty,
  -- but {T_i, β} ≠ ∅. Element analysis: cf(c) ⊆ Acc(T_i), excludes T_i (root)
  -- and β (h_T_i_no_β). cf(c') ⊆ Acc(T_j), excludes T_j (root) and T_i (h_T_j_no_T_i).
  -- Together: every elt of cf(c) is neither T_i nor β (so cf(c) = 0); similarly
  -- every elt of cf(c') is not T_i, so cf(c') ⊆ {β}. Then total ∈ {0, {β}, {β, β}, ...},
  -- never = {T_i, β}.
  have h_ss : mergePost (R := R) (α := α) T_i β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
      = 0 := by
    rw [Fintype.sum_mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- From cf(c) + cf(c') = {T_i, β}: T_i ∈ LHS.
    have h_T_i_mem : T_i ∈ CutShape.cutForest c + CutShape.cutForest c' := by
      rw [h_eq]
      exact Multiset.mem_cons_self _ _
    rcases Multiset.mem_add.mp h_T_i_mem with h | h
    · exact CutShape.not_mem_cutForest_self c h
    · exact h_T_j_no_T_i c' h
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [add_zero, zero_add]

/-- **Sideward Merge case 2(b) realization, full residual workspace**
    (M-C-B Lemma 1.4.4, p. 54). Generalization of `mergeOp_sideward_2b_pair`
    to arbitrary residual workspace `Fhat` via the factor-out pattern.
    The existing `mergeOp_factor_out_singleton` is parametric in (S, S')
    and applies directly to (S, S') = (T_i, β) with `MergeTargetFreeWorkspace
    T_i β Fhat` providing the per-spectator disjointness. -/
theorem mergeOp_sideward_2b {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j β T_j_q : TraceTree α Unit)
    (c_β : CutShape T_j) (Fhat : TraceForest α Unit)
    (h_cut : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique : ∀ c : CutShape T_j, c ≠ c_β →
                CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_T_i : ∀ c : CutShape T_j, T_i ∉ CutShape.cutForest c)
    (h_distinct : T_i ≠ T_j)
    (h_β_ne_Tj : β ≠ T_j)
    (h_F_disjoint : MergeTargetFreeWorkspace T_i β Fhat) :
    mergeOp (R := R) T_i β
        (forestToHc (({T_i, T_j} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node T_i β, T_j_q} : TraceForest α Unit) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    exact mergeOp_sideward_2b_pair T_i T_j β T_j_q c_β
      h_cut h_remainder h_unique h_T_i_no_β h_T_j_no_T_i h_distinct h_β_ne_Tj
  | cons T Fhat' ih =>
    have hT : MergeTargetFree T_i β T := MergeTargetFreeWorkspace.head h_F_disjoint
    have ih' := ih (MergeTargetFreeWorkspace.of_cons h_F_disjoint)
    have h_lhs_eq : ({T_i, T_j} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({T_i, T_j} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    have h_rhs_eq : ({.node T_i β, T_j_q} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({.node T_i β, T_j_q} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT]
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-- **Sideward Merge case 3(b) realization, F̂ = ∅ subcase** (M-C-B Lemma
    1.4.4, p. 54). 2-tree-workspace base case for the configuration where
    both α and β are accessible terms of distinct components T_i ≠ T_j.
    The operator `δ_{α, β}` selects `(α ⊔ β) ⊗ (T_i/α ⊔ T_j/β ⊔ F̂)`,
    producing `{M(α, β), T_i/α, T_j/β}`.

    Surviving cross-term: cut_{c_α} × cut_{c_β}, contributing
    `forestToHc {.node α β} * forestToHc {T_i_q} * forestToHc {T_j_q}`.
    All other cross-terms vanish via membership analysis on `{α, β}`. -/
theorem mergeOp_sideward_3b_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j α_t β T_i_q T_j_q : TraceTree α Unit)
    (c_α : CutShape T_i) (c_β : CutShape T_j)
    (h_cut_α : IsSingleEdgeAccessibleCut T_i α_t c_α)
    (h_cut_β : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder_α : CutShape.remainderDeletion c_α = some T_i_q)
    (h_remainder_β : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique_α : ∀ c : CutShape T_i, c ≠ c_α →
                  CutShape.cutForest c ≠ ({α_t} : TraceForest α Unit))
    (h_unique_β : ∀ c : CutShape T_j, c ≠ c_β →
                  CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_α : ∀ c : CutShape T_j, α_t ∉ CutShape.cutForest c)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β)
    (h_distinct : T_i ≠ T_j) :
    mergeOp (R := R) α_t β
        (forestToHc ({T_i, T_j} : TraceForest α Unit))
      = forestToHc ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
        * forestToHc (R := R) ({T_j_q} : TraceForest α Unit) := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comulDelAlgHom_pair,
      comulTreeDel_eq_prim_add_sum, comulTreeDel_eq_prim_add_sum]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Term 1 (prim × prim): F_left = {T_i, T_j} ≠ {α, β} (α ≠ T_i, etc.)
  have h_pp : mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- {T_i, T_j} = {α, β} ⟹ T_i ∈ {α, β}
    have h_T_i_mem : T_i ∈ ({T_i, T_j} : TraceForest α Unit) :=
      Multiset.mem_cons_self _ _
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 2 (prim × cut): F_left = {T_i} + cf(c') ≠ {α, β} (T_i ∉ {α, β}).
  have h_ps : mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = 0 := by
    rw [Finset.mul_sum]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c' _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, one_mul]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- T_i ∈ ({T_i} + cf c'), so T_i ∈ {α, β}.
    have h_T_i_mem : T_i ∈ ({T_i} : TraceForest α Unit) + CutShape.cutForest c' :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 3 (cut × prim): symmetric — T_j ∉ {α, β}.
  have h_sp : mergePost (R := R) (α := α) α_t β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
      = 0 := by
    rw [Finset.sum_mul]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    have h_T_j_mem : T_j ∈ CutShape.cutForest c + ({T_j} : TraceForest α Unit) :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))
    rw [h_eq] at h_T_j_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_j_mem
    rcases h_T_j_mem with h | h
    · exact h_α_ne_Tj h.symm
    · exact h_β_ne_Tj h.symm
  -- Term 4 (cut × cut): only (c_α, c_β) survives.
  have h_ss : mergePost (R := R) (α := α) α_t β
        ((∑ c : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c))
          * (∑ c' : CutShape T_j,
              forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
                deletionRightChannel (R := R) (CutShape.remainderDeletion c')))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
        * forestToHc (R := R) ({T_j_q} : TraceForest α Unit) := by
    rw [Fintype.sum_mul_sum]
    simp only [map_sum]
    rw [Finset.sum_eq_single c_α]
    · rw [Finset.sum_eq_single c_β]
      · -- (c_α, c_β): the surviving cross-term.
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
        rw [show CutShape.cutForest c_α + CutShape.cutForest c_β
              = ({α_t, β} : TraceForest α Unit) from by
            rw [show CutShape.cutForest c_α = ({α_t} : TraceForest α Unit) from h_cut_α]
            rw [show CutShape.cutForest c_β = ({β} : TraceForest α Unit) from h_cut_β]
            rfl]
        rw [mergePost_basis_tensor, if_pos rfl]
        rw [h_remainder_α, h_remainder_β]
        show forestToHc (R := R) ({.node α_t β} : TraceForest α Unit) *
              (forestToHc (R := R) ({T_i_q} : TraceForest α Unit) *
                forestToHc (R := R) ({T_j_q} : TraceForest α Unit)) = _
        rw [← mul_assoc]
      · -- c' ≠ c_β at the c_α slot: cf(c_α) + cf(c') ≠ {α, β} (c_α gives {α}, c' ≠ {β})
        intro c' _ hc'_ne
        rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
        rw [mergePost_basis_tensor, if_neg]
        intro h_eq
        apply h_unique_β c' hc'_ne
        rw [show CutShape.cutForest c_α = ({α_t} : TraceForest α Unit) from h_cut_α] at h_eq
        have h_target : ({α_t, β} : TraceForest α Unit)
                      = ({α_t} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
        rw [h_target] at h_eq
        exact Multiset.add_right_inj.mp h_eq
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- c ≠ c_α at the outer slot: cf(c) + cf(c') ≠ {α, β} for all c'
      intro c _ hc_ne
      apply Finset.sum_eq_zero
      intro c' _
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      -- α ∈ cf(c) + cf(c') = {α, β}
      have h_α_mem : α_t ∈ CutShape.cutForest c + CutShape.cutForest c' := by
        rw [h_eq]
        exact Multiset.mem_cons_self _ _
      rcases Multiset.mem_add.mp h_α_mem with h | h
      · -- α_t ∈ cf(c). Show cf(c) = {α_t} via element-count analysis on
        -- cf(c) + cf(c') = {α_t, β}, then contradict h_unique_α.
        apply h_unique_α c hc_ne
        -- Strategy: prove cf(c) = {α_t} by Multiset.ext (count-equality on each x).
        apply Multiset.ext.mpr
        intro x
        -- Both sides have count 0 except at x = α_t (count 1).
        -- count x (cf(c) + cf(c')) = count x cf(c) + count x cf(c') = count x {α_t, β}.
        have h_count_sum := congrArg (Multiset.count x) h_eq
        rw [Multiset.count_add] at h_count_sum
        by_cases hx_α : x = α_t
        · -- x = α_t: count α_t in cf(c) = 1.
          subst hx_α
          rw [Multiset.count_singleton_self]
          -- count x ({x, β}) = 1 (since x ≠ β; here `x` is α_t after subst)
          have h_count_target :
              Multiset.count x (({x, β} : TraceForest α Unit)) = 1 := by
            simp [Multiset.count_cons_self, Multiset.count_singleton, h_α_ne_β]
          rw [h_count_target] at h_count_sum
          -- count x (cf c') = 0 (h_T_j_no_α)
          have h_count_c' : Multiset.count x (CutShape.cutForest c') = 0 :=
            Multiset.count_eq_zero.mpr (h_T_j_no_α c')
          rw [h_count_c', add_zero] at h_count_sum
          exact h_count_sum
        · -- x ≠ α_t: count = 0 in {α_t}; need count = 0 in cf(c).
          rw [Multiset.count_singleton]
          rw [if_neg hx_α]
          by_cases hx_β : x = β
          · -- x = β: count β cf(c) = 0 by h_T_i_no_β
            subst hx_β
            exact Multiset.count_eq_zero.mpr (h_T_i_no_β c)
          · -- x ∉ {α_t, β}: count x {α_t, β} = 0, so count x cf(c) = 0.
            have h_count_target_zero :
                Multiset.count x (({α_t, β} : TraceForest α Unit)) = 0 := by
              show Multiset.count x (α_t ::ₘ ({β} : TraceForest α Unit)) = 0
              rw [Multiset.count_cons, Multiset.count_singleton,
                  if_neg hx_α, if_neg hx_β]
            rw [h_count_target_zero] at h_count_sum
            exact (Nat.add_eq_zero_iff.mp h_count_sum).1
      · exact h_T_j_no_α c' h
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_pp, h_ps, h_sp, h_ss]
  simp only [zero_add, add_zero]

/-- **Sideward Merge case 3(b) realization, full residual workspace**
    (M-C-B Lemma 1.4.4, p. 54). Generalization of `mergeOp_sideward_3b_pair`
    via the factor-out pattern, parameterised on (S, S') = (α_t, β). -/
theorem mergeOp_sideward_3b {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i T_j α_t β T_i_q T_j_q : TraceTree α Unit)
    (c_α : CutShape T_i) (c_β : CutShape T_j) (Fhat : TraceForest α Unit)
    (h_cut_α : IsSingleEdgeAccessibleCut T_i α_t c_α)
    (h_cut_β : IsSingleEdgeAccessibleCut T_j β c_β)
    (h_remainder_α : CutShape.remainderDeletion c_α = some T_i_q)
    (h_remainder_β : CutShape.remainderDeletion c_β = some T_j_q)
    (h_unique_α : ∀ c : CutShape T_i, c ≠ c_α →
                  CutShape.cutForest c ≠ ({α_t} : TraceForest α Unit))
    (h_unique_β : ∀ c : CutShape T_j, c ≠ c_β →
                  CutShape.cutForest c ≠ ({β} : TraceForest α Unit))
    (h_T_i_no_β : ∀ c : CutShape T_i, β ∉ CutShape.cutForest c)
    (h_T_j_no_α : ∀ c : CutShape T_j, α_t ∉ CutShape.cutForest c)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j)
    (h_α_ne_β : α_t ≠ β)
    (h_distinct : T_i ≠ T_j)
    (h_F_disjoint : MergeTargetFreeWorkspace α_t β Fhat) :
    mergeOp (R := R) α_t β
        (forestToHc (({T_i, T_j} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node α_t β, T_i_q, T_j_q} : TraceForest α Unit) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    -- The pair version produces forestToHc {.node α β} * forestToHc {T_i_q} * forestToHc {T_j_q}.
    -- Convert to forestToHc {.node α β, T_i_q, T_j_q}.
    have h_pair := mergeOp_sideward_3b_pair (R := R)
      T_i T_j α_t β T_i_q T_j_q c_α c_β
      h_cut_α h_cut_β h_remainder_α h_remainder_β h_unique_α h_unique_β
      h_T_i_no_β h_T_j_no_α h_α_ne_Ti h_α_ne_Tj h_β_ne_Ti h_β_ne_Tj h_α_ne_β h_distinct
    rw [h_pair]
    rw [show forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
            * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
            * forestToHc (R := R) ({T_j_q} : TraceForest α Unit)
        = forestToHc (R := R) (({.node α_t β} : TraceForest α Unit)
                                + ({T_i_q} : TraceForest α Unit)
                                + ({T_j_q} : TraceForest α Unit)) from by
        rw [forestToHc_add, forestToHc_add]]
    congr 1
  | cons T Fhat' ih =>
    have hT : MergeTargetFree α_t β T := MergeTargetFreeWorkspace.head h_F_disjoint
    have ih' := ih (MergeTargetFreeWorkspace.of_cons h_F_disjoint)
    have h_lhs_eq : ({T_i, T_j} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({T_i, T_j} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    have h_rhs_eq : ({.node α_t β, T_i_q, T_j_q} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({.node α_t β, T_i_q, T_j_q} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT]
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-- **Sideward Merge case 3(a) realization** ("Countercyclic-like Merge",
    M-C-B Lemma 1.4.5, p. 55). Both α and β are disjoint accessible terms
    of the *same* component T_i. The operator `δ_{α, β}` selects
    `T_v ⊔ T_w ⊗ (T_i/(T_v ⊔ T_w) ⊔ F̂)`, producing
    `{M(α, β), T_i/(α ⊔ β)} + Fhat`.

    Proof strategy: the surviving cross-term comes from a single
    *2-edge* admissible cut on T_i (extracting both α ≃ T_v and
    β ≃ T_w as separate subforest elements), yielding `cutForest =
    {α, β}` as a 2-element multiset. This requires the substrate
    extension `IsTwoEdgeAccessibleCut T_i α β c` (hypothesis below):
    a cut whose cutForest contains exactly α and β as distinct
    elements. The mergePost cross-term selection criterion then becomes
    `cutForest c = {α, β}`. -/
def IsTwoEdgeAccessibleCut {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit) (c : CutShape T_i) : Prop :=
  CutShape.cutForest c = ({α_t, β} : TraceForest α Unit)

instance {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit) (c : CutShape T_i) :
    Decidable (IsTwoEdgeAccessibleCut T_i α_t β c) := by
  unfold IsTwoEdgeAccessibleCut; infer_instance

/-- **Sideward Merge case 3(a) realization, F̂ = ∅ subcase** ("Countercyclic-
    like Merge", M-C-B Lemma 1.4.5, p. 55). 1-tree-workspace base case for
    the configuration where both α and β are accessible terms of the same
    component T_i, extracted by a single 2-edge admissible cut.

    Surviving term: cut_c (the unique 2-edge cut producing {α, β}),
    contributing `forestToHc {.node α β} * forestToHc {T_i_q}`. -/
theorem mergeOp_sideward_3a_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i α_t β T_i_q : TraceTree α Unit)
    (c : CutShape T_i)
    (h_cut : IsTwoEdgeAccessibleCut T_i α_t β c)
    (h_remainder : CutShape.remainderDeletion c = some T_i_q)
    (h_unique : ∀ c' : CutShape T_i, c' ≠ c →
                CutShape.cutForest c' ≠ ({α_t, β} : TraceForest α Unit))
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i)
    (_h_α_ne_β : α_t ≠ β) :
    mergeOp (R := R) α_t β (forestToHc ({T_i} : TraceForest α Unit))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit) := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({T_i} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [show comulDelAlgHom (R := R) (α := α)
            (forestToHc (R := R) ({T_i} : TraceForest α Unit))
          = comulTreeDel (R := R) T_i from by
      unfold forestToHc
      rw [comulDelAlgHom_apply_single, comulForestDel_singleton]]
  rw [comulTreeDel_eq_prim_add_sum]
  simp only [map_add]
  -- Term 1 (prim_{T_i}): F_left = {T_i} ≠ {α, β} since T_i ∉ {α, β}.
  have h_p : mergePost (R := R) (α := α) α_t β
        (forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)) = 0 := by
    rw [mergePost_basis_tensor, if_neg]
    intro h_eq
    -- T_i ∈ {T_i} = {α, β}, so T_i = α or T_i = β; both contradicted.
    have h_T_i_mem : T_i ∈ ({T_i} : TraceForest α Unit) :=
      Multiset.mem_singleton.mpr rfl
    rw [h_eq] at h_T_i_mem
    rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
    rcases h_T_i_mem with h | h
    · exact h_α_ne_Ti h.symm
    · exact h_β_ne_Ti h.symm
  -- Term 2 (sum c'): only c' = c survives (uniqueness), contributes the answer.
  have h_s : mergePost (R := R) (α := α) α_t β
        (∑ c' : CutShape T_i,
            forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
              deletionRightChannel (R := R) (CutShape.remainderDeletion c'))
      = forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
        * forestToHc (R := R) ({T_i_q} : TraceForest α Unit) := by
    simp only [map_sum]
    rw [Finset.sum_eq_single c]
    · -- c' = c: surviving term.
      rw [show CutShape.cutForest c = ({α_t, β} : TraceForest α Unit) from h_cut]
      rw [mergePost_basis_tensor, if_pos rfl, h_remainder]
      rfl
    · intro c' _ hc'_ne
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      exact h_unique c' hc'_ne h_eq
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h_p, h_s]
  simp only [zero_add]

/-- **Sideward Merge case 3(a) realization, full residual workspace**
    (M-C-B Lemma 1.4.5, p. 55). Generalization of `mergeOp_sideward_3a_pair`
    via the factor-out pattern, parameterised on (S, S') = (α_t, β). -/
theorem mergeOp_sideward_3a {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (T_i α_t β T_i_q : TraceTree α Unit)
    (c : CutShape T_i) (Fhat : TraceForest α Unit)
    (h_cut : IsTwoEdgeAccessibleCut T_i α_t β c)
    (h_remainder : CutShape.remainderDeletion c = some T_i_q)
    (h_unique : ∀ c' : CutShape T_i, c' ≠ c →
                CutShape.cutForest c' ≠ ({α_t, β} : TraceForest α Unit))
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i)
    (h_α_ne_β : α_t ≠ β)
    (h_F_disjoint : MergeTargetFreeWorkspace α_t β Fhat) :
    mergeOp (R := R) α_t β
        (forestToHc (({T_i} : TraceForest α Unit) + Fhat))
      = forestToHc (({.node α_t β, T_i_q} : TraceForest α Unit) + Fhat) := by
  induction Fhat using Multiset.induction with
  | empty =>
    rw [add_zero, add_zero]
    have h_pair := mergeOp_sideward_3a_pair (R := R)
      T_i α_t β T_i_q c h_cut h_remainder h_unique h_α_ne_Ti h_β_ne_Ti h_α_ne_β
    rw [h_pair]
    rw [show forestToHc (R := R) ({.node α_t β} : TraceForest α Unit)
            * forestToHc (R := R) ({T_i_q} : TraceForest α Unit)
        = forestToHc (R := R) (({.node α_t β} : TraceForest α Unit)
                                + ({T_i_q} : TraceForest α Unit)) from by
        rw [forestToHc_add]]
    congr 1
  | cons T Fhat' ih =>
    have hT : MergeTargetFree α_t β T := MergeTargetFreeWorkspace.head h_F_disjoint
    have ih' := ih (MergeTargetFreeWorkspace.of_cons h_F_disjoint)
    have h_lhs_eq : ({T_i} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({T_i} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    have h_rhs_eq : ({.node α_t β, T_i_q} : TraceForest α Unit) + T ::ₘ Fhat'
                  = ({T} : TraceForest α Unit)
                    + (({.node α_t β, T_i_q} : TraceForest α Unit) + Fhat') := by
      rw [show T ::ₘ Fhat' = ({T} : TraceForest α Unit) + Fhat' from rfl]; abel
    rw [h_lhs_eq, h_rhs_eq,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _,
        forestToHc_add (R := R) ({T} : TraceForest α Unit) _]
    rw [mergeOp_factor_out_singleton hT]
    exact congrArg (forestToHc (R := R) ({T} : TraceForest α Unit) * ·) ih'

/-! ## §4.1: Cost-suppression theorems (sorry-free as of 0.230.804)

Per MCB §1.5 (Minimal Search via ε-weighted derivation cost — rules 1-5
of §1.5.2 with eq. (1.5.1)-(1.5.2), pp. 59-60), Sideward configurations
are *subdominant and suppressed* in the ε → 0 limit because the cost of
extracting an accessible term at depth d carries weight ε^d, which goes
to 0 strictly faster than the EM cost (= ε^0 = 1) for d > 0.

For Sideward 2(b), the depth d > 0 of β inside T_j gives ε^d → 0.
For Sideward 3(a), 3(b), both α and β at depth ≥ 1 give ε^{d_α+d_β} → 0.
For IM (case 2(a)), the depth d cancels with the quotient operation's
weight ε^{-d}, so the leading-order term survives at ε^0 = 1.

The cost-suppression theorems below state that **at literal ε = 0**, the
Sideward outputs are zero. Note: this is *pointwise at ε = 0*, not a
limit theorem — but the two coincide for d > 0 because `0^d = 0` for
d > 0. The proof mechanism: at ε = 0, `comulTreeDel_eps 0 T` collapses
to the primitive part `(T ⊗ 1) + (1 ⊗ T)` (cuts vanish from the
ε-weighted coproduct); no primitive cross-term has LEFT-channel forest
matching the Sideward target.

**Caveat — NCL is needed for IM-vs-Sideward 2(b)** (MCB Remark 1.6.9, p. 71):
"the Sideward Merge of type 2(b) cannot be distinguished from Internal
Merge, solely on the basis of the size measures of Definition 1.2.2".
Minimal Search alone (this section) is necessary but not sufficient;
the No Complexity Loss principle (§2.7 above, Prop 1.6.10) is what
formally distinguishes IM from Sideward 2(b).

**MCB Prop 1.5.1** (book p. 60) is the anchor: bullet 3 states "in the
limit ε → 0, only derivations in which all the Merge operations are
Internal Merge and External Merge remain." The theorems below implement
the *negative direction* (Sideward → 0); the positive direction
(IM survives at weight 1) is queued as Phase 7g — requires extending
the ε-weighted substrate with rule 2's negative-depth weight on the
right channel (`ε^{-d_v}` on `T/T_v`). -/

/-- **Cost-suppression for Sideward 2(b)** (MCB §1.5.3 + §1.4.5).
    At ε = 0, applying `mergeOp_eps 0 T_i β` to the workspace
    `{T_i, T_j}` (where β is an accessible term of T_j, not a component)
    yields **0** — the Sideward 2(b) realization of `mergeOp` (which
    consumes the cut producing β) is entirely absent at ε = 0 because
    `comulTreeDel_eps 0 T_j` reduces to the primitive part
    `(T_j ⊗ 1) + (1 ⊗ T_j)` (no cut subforests).

    No primitive cross-term of (prim T_i) × (prim T_j) has LEFT-channel
    forest equal to `{T_i, β}` (since β ∉ {T_i, T_j} when β ≠ T_i and
    β ≠ T_j); `mergePost` annihilates all four. -/
theorem mergeOp_eps_zero_for_sideward_2b {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i T_j β : TraceTree α Unit)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp_eps (R := R) 0 T_i β
        (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0 := by
  show (mergePost (R := R) (α := α) T_i β ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  show mergePost (R := R) (α := α) T_i β
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({T_i, T_j} : TraceForest α Unit) (1 : R))) = 0
  rw [comulDelAlgHom_eps_apply_single]
  show mergePost (R := R) (α := α) T_i β
        ((({T_i, T_j} : TraceForest α Unit).map
          (comulTreeDel_eps (R := R) 0)).prod) = 0
  rw [show (({T_i, T_j} : TraceForest α Unit).map (comulTreeDel_eps (R := R) 0)).prod
      = comulTreeDel_eps (R := R) 0 T_i * comulTreeDel_eps (R := R) 0 T_j from
    Multiset.prod_pair _ _]
  rw [comulTreeDel_eps_zero, comulTreeDel_eps_zero]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- 4 cross-terms; LEFT-channel forest = {T_i, T_j}, {T_i}, {T_j}, ∅ — all ≠ {T_i, β}.
  -- Term 1 (prim × prim): LEFT = {T_i, T_j} ≠ {T_i, β} (since T_j ≠ β).
  rw [show mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
      rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      apply h_β_ne_Tj
      have h_target : ({T_i, β} : TraceForest α Unit)
                    = ({T_i} : TraceForest α Unit) + ({β} : TraceForest α Unit) := rfl
      have h_lhs : ({T_i, T_j} : TraceForest α Unit)
                 = ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit) := rfl
      rw [h_lhs, h_target] at h_eq
      exact (Multiset.singleton_inj.mp (Multiset.add_right_inj.mp h_eq)).symm]
  -- Term 2 (prim × empty): LEFT = {T_i}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) T_i β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_i} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({T_i, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 3 (empty × prim): LEFT = {T_j}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) T_i β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_j} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({T_i, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 4 (empty × empty): LEFT = ∅; cardinality 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) T_i β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : (0 : TraceForest α Unit).card = 0 := Multiset.card_zero
      have h_card_rhs : ({T_i, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  simp only [add_zero]

/-- **Cost-suppression for Sideward 3(a)** (MCB §1.5.3 + §1.4.6).
    At ε = 0, applying `mergeOp_eps 0 α_t β` to the single-component
    workspace `{T_i}` (where α_t, β are accessible terms of T_i) yields
    **0**. Same reasoning: at ε = 0 only the primitive part of
    `comulTreeDel_eps 0 T_i = (T_i ⊗ 1) + (1 ⊗ T_i)` survives; neither
    primitive contributes LEFT = {α_t, β}. -/
theorem mergeOp_eps_zero_for_sideward_3a {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i α_t β : TraceTree α Unit)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_β_ne_Ti : β ≠ T_i) :
    mergeOp_eps (R := R) 0 α_t β
        (forestToHc ({T_i} : TraceForest α Unit)) = 0 := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({T_i} : TraceForest α Unit)) = 0
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  show mergePost (R := R) (α := α) α_t β
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({T_i} : TraceForest α Unit) (1 : R))) = 0
  rw [comulDelAlgHom_eps_apply_single]
  show mergePost (R := R) (α := α) α_t β
        ((({T_i} : TraceForest α Unit).map
          (comulTreeDel_eps (R := R) 0)).prod) = 0
  rw [Multiset.map_singleton, Multiset.prod_singleton, comulTreeDel_eps_zero]
  -- comulTreeDel_eps 0 T_i = (T_i ⊗ 1) + (1 ⊗ T_i); both vanish under mergePost.
  simp only [map_add]
  -- Term 1 (T_i ⊗ 1): LEFT = {T_i}, cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        (forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
        = 0 from by
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_i} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 2 (1 ⊗ T_i): LEFT = ∅, cardinality 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
        = 0 from by
      rw [show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : (0 : TraceForest α Unit).card = 0 := Multiset.card_zero
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  rw [add_zero]

/-- **Cost-suppression for Sideward 3(b)** (MCB §1.5.3 + §1.4.5).
    At ε = 0, applying `mergeOp_eps 0 α_t β` to a 2-component workspace
    `{T_i, T_j}` where α_t ∈ Acc(T_i), β ∈ Acc(T_j) yields **0**. Same
    reasoning as 2(b): only primitive parts survive at ε = 0, and no
    primitive cross-term has LEFT = {α_t, β}. -/
theorem mergeOp_eps_zero_for_sideward_3b {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α]
    (T_i T_j α_t β : TraceTree α Unit)
    (h_α_ne_Ti : α_t ≠ T_i)
    (h_α_ne_Tj : α_t ≠ T_j)
    (h_β_ne_Ti : β ≠ T_i)
    (h_β_ne_Tj : β ≠ T_j) :
    mergeOp_eps (R := R) 0 α_t β
        (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0 := by
  show (mergePost (R := R) (α := α) α_t β ∘ₗ
        (comulDelAlgHom_eps (0 : R)).toLinearMap)
       (forestToHc ({T_i, T_j} : TraceForest α Unit)) = 0
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  show mergePost (R := R) (α := α) α_t β
        (comulDelAlgHom_eps (R := R) (α := α) (0 : R)
          (Finsupp.single ({T_i, T_j} : TraceForest α Unit) (1 : R))) = 0
  rw [comulDelAlgHom_eps_apply_single]
  show mergePost (R := R) (α := α) α_t β
        ((({T_i, T_j} : TraceForest α Unit).map
          (comulTreeDel_eps (R := R) 0)).prod) = 0
  rw [show (({T_i, T_j} : TraceForest α Unit).map (comulTreeDel_eps (R := R) 0)).prod
      = comulTreeDel_eps (R := R) 0 T_i * comulTreeDel_eps (R := R) 0 T_j from
    Multiset.prod_pair _ _]
  rw [comulTreeDel_eps_zero, comulTreeDel_eps_zero]
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- 4 cross-terms; LEFT-channel forests {T_i, T_j}, {T_i}, {T_j}, ∅ — all ≠ {α_t, β}.
  -- Term 1 (prim × prim): LEFT = {T_i, T_j}. T_i ∉ {α_t, β} → ≠.
  rw [show mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← forestToHc_add, mul_one]
      rw [show ({T_i} : TraceForest α Unit) + ({T_j} : TraceForest α Unit)
          = ({T_i, T_j} : TraceForest α Unit) from rfl]
      rw [mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_T_i_mem : T_i ∈ ({T_i, T_j} : TraceForest α Unit) :=
        Multiset.mem_cons_self _ _
      rw [h_eq] at h_T_i_mem
      rw [show ({α_t, β} : TraceForest α Unit) = α_t ::ₘ ({β} : TraceForest α Unit) from rfl,
          Multiset.mem_cons, Multiset.mem_singleton] at h_T_i_mem
      rcases h_T_i_mem with h | h
      · exact h_α_ne_Ti h.symm
      · exact h_β_ne_Ti h.symm]
  -- Term 2 (prim × empty): LEFT = {T_i}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        ((forestToHc (R := R) ({T_i} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_i} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 3 (empty × prim): LEFT = {T_j}; cardinality 1 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * (forestToHc (R := R) ({T_j} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : ({T_j} : TraceForest α Unit).card = 1 := Multiset.card_singleton _
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  -- Term 4 (empty × empty): LEFT = ∅; cardinality 0 ≠ 2.
  rw [show mergePost (R := R) (α := α) α_t β
        (((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_i} : TraceForest α Unit))
          * ((1 : Hc R α) ⊗ₜ[R] forestToHc (R := R) ({T_j} : TraceForest α Unit)))
        = 0 from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          show (1 : Hc R α) = forestToHc (R := R) (0 : TraceForest α Unit) from
            forestToHc_zero.symm,
          mergePost_basis_tensor, if_neg]
      intro h_eq
      have h_card_lhs : (0 : TraceForest α Unit).card = 0 := Multiset.card_zero
      have h_card_rhs : ({α_t, β} : TraceForest α Unit).card = 2 := rfl
      rw [h_eq] at h_card_lhs
      omega]
  simp only [add_zero]

end Minimalist.Merge
