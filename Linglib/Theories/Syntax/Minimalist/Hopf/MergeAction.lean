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
(commits 0.230.741-0.230.743). Internal Merge is documented as a
composition gap (see §3 below).

Both EM bridges specialize a general algebraic result `mergeOp_pair`,
which proves `mergeOp S S' (forestToHc {S, S'}) = forestToHc {.node S S'}`
for any pair `(S, S') : TraceTree α Unit` over any commutative
semiring `R`. The proof factors through:

- `comulDelAlgHom_pair` (substrate): `Δ^d({S, S'}) = Δ^d(S) · Δ^d(S')`.
- `mergePost_basis_tensor` (`Merge.lean`): basis-tensor evaluation of
  `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}` returns `forestToHc {.node S S'} * r` if
  the LEFT channel is `{S, S'}`, else `0`.
- 4 cross-term reductions (`mergePost_pair_*`): expand `Δ^d(S) · Δ^d(S')`
  into `(prim + sum) · (prim + sum)`, prove each cross-category
  contributes 0 except `prim · prim`. Cross-term elimination uses
  `cutForest_ne_singleton_self` and `cutForest_add_pair_ne_pair` from
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
realization via `mergeOp`. -/

/-- The singleton workspace containing the embedding of `so` as the
    sole tree. The basis vector `forestToHc {so.toHc}` in `Hc ℤ LIToken`. -/
noncomputable def singletonWorkspace (so : Minimalist.SyntacticObject) :
    Hc ℤ LIToken :=
  forestToHc ({so.toHc} : TraceForest LIToken Unit)

/-! ## §2: External Merge bridge

For `Step.emR item` applied to `current`, the result is
`.node current item`. The algebraic side: `mergeOp current.toH item.toH`
applied to a workspace containing both `current` and `item` should
produce the singleton workspace of `.node current item`.

**Proof strategy** (M-C-B Lemma 1.3.6):

1. Unfold `mergeOp = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d`.
2. Apply `comulDelAlgHom_pair`: `Δ^d({S, S'}) = Δ^d(S) · Δ^d(S')`.
3. Expand each `Δ^d(T) = T ⊗ 1 + ∑_c (cutForest c) ⊗ rChan(c)`.
4. Multiply: 4 cross-categories of terms. For each elementary tensor
   `forestToHc F ⊗ r` produced, `mergePost_basis_tensor` gives
   `forestToHc {.node S S'} * r` if `F = {S, S'}`, else `0`.
5. **Cross-term elimination** via the structural lemmas:
   - `prim_S * prim_{S'}`: `F = {S, S'}` ✓ — contributes the answer.
   - `prim_S * cut_{c'}`: `F = {S} + cutForest c'`. For this to equal
     `{S, S'}`, need `cutForest c' = {S'}` — impossible by
     `cutForest_ne_singleton_self` (a cut on `S'` cannot extract `S'` itself).
   - `cut_c * prim_{S'}`: symmetric, `cutForest c = {S}` impossible.
   - `cut_c * cut_{c'}`: `F = cutForest c + cutForest c'`. Cannot equal
     `{S, S'}` by `cutForest_add_pair_ne_pair` (size argument).
6. Only the primitive term survives, giving `forestToHc {.node S S'} * 1
   = forestToHc {.node S S'}`.

The proof is structured around a general `mergeOp_pair` lemma that
proves the result for any pair `(S, S') : TraceTree α Unit` over any
commutative semiring `R`. The Minimalism-specific bridges
(`mergeOp_emR_matches_Step`, `mergeOp_emL_matches_Step`) specialize
this and handle the `SyntacticObject ↔ TraceTree` translation. -/

/-- **Algebraic Merge on a 2-tree workspace** (M-C-B Lemma 1.3.6,
    general substrate version). For any pair `(S, S') : TraceTree α Unit`,
    `mergeOp S S'` applied to the basis vector `forestToHc {S, S'}`
    yields `forestToHc {.node S S'}`. -/
theorem mergeOp_pair {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]
    (S S' : TraceTree α Unit) :
    mergeOp (R := R) S S' (forestToHc ({S, S'} : TraceForest α Unit))
      = forestToHc ({.node S S'} : TraceForest α Unit) := by
  -- Step 1: reduce mergeOp to the post-coproduct chain on
  -- `comulTreeDel S * comulTreeDel S'`.
  show (hcMulLin (R := R) (α := α)
         ∘ₗ TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
         ∘ₗ deltaMatch (R := R) S S' ∘ₗ comulDelAlgHom.toLinearMap)
       (forestToHc ({S, S'} : TraceForest α Unit)) = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, comulDelAlgHom_pair]
  -- Step 2: define abbreviations for the coproduct decomposition.
  set primS : Hc R α ⊗[R] Hc R α :=
    forestToHc (R := R) ({S} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α) with hprimS
  set primS' : Hc R α ⊗[R] Hc R α :=
    forestToHc (R := R) ({S'} : TraceForest α Unit) ⊗ₜ[R] (1 : Hc R α) with hprimS'
  set sumS : Hc R α ⊗[R] Hc R α :=
    ∑ c : CutShape S,
      forestToHc (R := R) (CutShape.cutForest c) ⊗ₜ[R]
        deletionRightChannel (R := R) (CutShape.remainderDeletion c) with hsumS
  set sumS' : Hc R α ⊗[R] Hc R α :=
    ∑ c' : CutShape S',
      forestToHc (R := R) (CutShape.cutForest c') ⊗ₜ[R]
        deletionRightChannel (R := R) (CutShape.remainderDeletion c') with hsumS'
  have hcompS : comulTreeDel (R := R) S = primS + sumS := rfl
  have hcompS' : comulTreeDel (R := R) S' = primS' + sumS' := rfl
  rw [hcompS, hcompS']
  -- Step 3: distribute multiplication into 4 cross-terms and push linearity
  -- through the 3-layer chain (hcMulLin ∘ TensorProduct.map ∘ deltaMatch).
  rw [add_mul, mul_add, mul_add]
  simp only [map_add]
  -- Step 4: each of the 4 cross-terms reduces via the per-term lemmas.
  rw [mergePost_pair_prim_prim S S',
      mergePost_pair_prim_sum S S',
      mergePost_pair_sum_prim S S',
      mergePost_pair_sum_sum S S']
  -- Cleanup: answer + 0 + 0 + 0 = answer.
  rw [add_zero, add_zero, add_zero]

/-- **External Merge bridge (right-complement)** (M-C-B Lemma 1.3.6).
    `mergeOp current.toHc item.toHc` applied to the 2-tree workspace
    `{current.toHc, item.toHc}` yields the singleton workspace of
    `.node current item` = `(Step.emR item).apply current`. -/
theorem mergeOp_emR_matches_Step
    (current item : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) current.toHc item.toHc
        (forestToHc ({current.toHc, item.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emR item).apply current).toH.anon (fun _ => ())}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  rfl

/-- **External Merge bridge (left-specifier)** (M-C-B Lemma 1.3.6,
    symmetric pair). `mergeOp item.toHc current.toHc` applied to
    `{item.toHc, current.toHc}` yields `.node item current`. -/
theorem mergeOp_emL_matches_Step
    (item current : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) item.toHc current.toHc
        (forestToHc ({item.toHc, current.toHc} : TraceForest LIToken Unit))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toH.anon (fun _ => ())}
        : TraceForest LIToken Unit) := by
  rw [mergeOp_pair]
  rfl

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
