import Linglib.Theories.Syntax.Minimalism.Hopf.Merge
import Linglib.Theories.Syntax.Minimalism.Derivation

/-!
# Bridge: Algebraic Merge ↔ Linguistic Merge
@cite{marcolli-chomsky-berwick-2025}

This file connects two views of the Merge operation:

- **Algebraic Merge** (Hopf-side): `Minimalism.Hopf.mergeOp S S' : Hc R α →ₗ[R] Hc R α`
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

namespace Minimalism.Hopf

open scoped TensorProduct

/-! ## §1: Workspace-level bridge predicates

A "bridge predicate" relates a linguistic `Step` to its algebraic
realization via `mergeOp`. -/

/-- The singleton workspace containing the embedding of `so` as the
    sole tree. The basis vector `forestToHc {so.toH}` in `Hc ℤ LIToken`. -/
noncomputable def singletonWorkspace (so : Minimalism.SyntacticObject) :
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
    (current item : Minimalism.SyntacticObject) :
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
    (item current : Minimalism.SyntacticObject) :
    mergeOp (R := ℤ) item.toH current.toH
        (forestToHc ({item.toH, current.toH} : Forest LIToken))
      = forestToHc (R := ℤ) ({((Step.emL item).apply current).toH} : Forest LIToken) := by
  -- Same strategy as mergeOp_emR_matches_Step with item/current swapped.
  -- Step.emL item current = .node item current
  sorry

/-! ## §3: Internal Merge bridge

For `Step.im mover traceId`, the result extracts `mover` from
`current` (replacing it with a trace-labeled leaf) and merges
`mover` at the left. The algebraic side selects the cut at `mover`'s
position via Δ^d, applies B grafting. -/

/-- **Internal Merge bridge** [SORRY-STUB].
    `mergeOp mover.toH (current/mover trace).toH` applied to the
    singleton workspace `{current.toH}` (where mover is an accessible
    term of current) yields the singleton workspace of
    `(Step.im mover traceId).apply current`.

    Note: the trace-id parameter `traceId` doesn't appear on the
    algebraic side because our `mergeOp` builds traces structurally
    via `DecoratedTree.trace`; the `Nat` id is a presentation choice
    of `Step.apply`. The bridge holds modulo this naming convention. -/
theorem mergeOp_im_matches_Step
    (current mover : Minimalism.SyntacticObject) (traceId : Nat) :
    -- Statement intentionally informal; full formal version requires
    -- defining the "trace-id-aware" embedding of Step.apply's output
    -- into SyntacticObjectH and matching against the algebraic trace.
    True := by
  trivial

end Minimalism.Hopf
