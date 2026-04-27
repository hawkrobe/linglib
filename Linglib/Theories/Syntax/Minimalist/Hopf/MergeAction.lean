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

Bridge **statements** are written here; **proofs are sorry'd**. The
proofs require:

1. Translating between `SyntacticObject` and `SyntacticObjectH`
   (= `DecoratedTree LIToken`) via `.toH` and `toSyntacticObject?`.
2. Computing the explicit form of `mergeOp S S' (forestToHc {T.toH})` —
   expanding `comulDelAlgHom` (a sum over `CutShape T.toH`), then
   `deltaMatch` (filtering to terms with cut forest = `{S, S'}`),
   then `graftBinaryAt` (replacing with `.node S S'`), then
   multiplication.
3. Showing the only surviving term matches `(Step.apply step T).toH`.

This is substantial linear-algebra-on-Finsupp work. Deferring to a
focused future session. The `mergeOp` definition (in `Merge.lean`) is
fully complete and usable — only the bridge proofs are pending.

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

/-! ## §1: Workspace-level bridge predicates

A "bridge predicate" relates a linguistic `Step` to its algebraic
realization via `mergeOp`. -/

/-- The singleton workspace containing the embedding of `so` as the
    sole tree. The basis vector `forestToHc {so.toH}` in `Hc ℤ LIToken`. -/
noncomputable def singletonWorkspace (so : Minimalist.SyntacticObject) :
    Hc ℤ LIToken :=
  forestToHc ({so.toH} : Forest LIToken)

/-! ## §2: External Merge bridge

For `Step.emR item` applied to `current`, the result is
`.node current item`. The algebraic side: `mergeOp current.toH item.toH`
applied to a workspace containing both `current` and `item` should
produce the singleton workspace of `.node current item`. -/

/-- **External Merge bridge (right-complement)** [SORRY-STUB].
    `mergeOp current.toH item.toH` applied to the 2-tree workspace
    `{current, item}` yields the singleton workspace of
    `.node current item` = `(Step.emR item).apply current`. -/
theorem mergeOp_emR_matches_Step
    (current item : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) current.toH item.toH
        (forestToHc ({current.toH, item.toH} : Forest LIToken))
      = forestToHc (R := ℤ) ({((Step.emR item).apply current).toH} : Forest LIToken) := by
  -- Proof strategy:
  -- 1. Unfold mergeOp = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d
  -- 2. Δ^d on the 2-tree workspace expands as Δ^d({current.toH}) * Δ^d({item.toH})
  --    by multiplicativity (comulDelAlgHom is an algebra hom)
  -- 3. Δ^d on a singleton tree T includes the primitive T ⊗ 1 + 1 ⊗ T
  --    plus admissible cuts of T
  -- 4. Multiplying the two singleton coproducts and filtering via
  --    δ_{S,S'} (= projection to {current.toH, item.toH} ⊗ ...)
  --    leaves a single term: {current.toH, item.toH} ⊗ 1
  -- 5. Applying B replaces {current.toH, item.toH} with .node current.toH item.toH
  -- 6. Multiplying by 1 (the right channel) gives {.node current.toH item.toH}
  -- 7. Step.emR item current = .node current item, and (.node current item).toH
  --    = .node current.toH item.toH (by SyntacticObject.toH definition)
  sorry

/-- **External Merge bridge (left-specifier)** [SORRY-STUB].
    Symmetric to `mergeOp_emR_matches_Step`. -/
theorem mergeOp_emL_matches_Step
    (item current : Minimalist.SyntacticObject) :
    mergeOp (R := ℤ) item.toH current.toH
        (forestToHc ({item.toH, current.toH} : Forest LIToken))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toH} : Forest LIToken) := by
  -- Same strategy as mergeOp_emR_matches_Step with item/current swapped.
  -- Step.emL item current = .node item current
  sorry

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
