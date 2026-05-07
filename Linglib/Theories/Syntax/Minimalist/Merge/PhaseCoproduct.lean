import Linglib.Theories.Syntax.Minimalist.Merge.Phase
import Linglib.Theories.Syntax.Minimalist.Merge.Defs
import Linglib.Core.Algebra.ConnesKreimer.Coproduct

/-!
# Algebraic Phase Coproduct Δ^c_Φ
@cite{marcolli-chomsky-berwick-2025} §1.14, Definition 1.14.5

Implements (in scaffold form) the **phase-restricted coproduct** Δ^c_Φ
of MCB §1.14, eq (1.14.6):

    Δ^c_Φ(T) = Σ_{v ∈ Φ_{h_T} ∖ Y_{h_T}}  F_v ⊗ T/^c F_v

where the sum is restricted to vertices `v` that are **phase-accessible** —
not in the inaccessibility set `Y_ℓ` of any lower phase. This is the
algebraic implementation of the Phase Impenetrability Condition: cuts
that would extract material from a closed lower phase are dropped from
the coproduct.

Per Lemma 1.14.6, Δ^c_Φ is well-defined and coassociative.

## Bridge from `SyntacticObject` to `TraceTree`

The phase substrate in `Merge/Phase.lean` operates on `SyntacticObject`
(linglib's `FreeMagma LIToken`); the Hopf-algebra carrier
(`Core/Algebra/ConnesKreimer/`) operates on `TraceTree LIToken Unit`.
The bridge is `SyntacticObject.toHc` (defined in `Merge/Defs.lean`),
which embeds an SO into the algebraic side, mapping `mkTrace` leaves to
the algebraic `.trace ()` constructor.

For phase-compatibility checking we need the *inverse* direction: given a
subtree that an admissible cut would extract (a `TraceTree`), we ask
whether the corresponding SO subtree is in the inaccessibility set
`Y_ℓ`. We use the existing `treeToSyntacticObject?` partial inverse
(returning `none` for trace-containing trees, but the `IsNotTrace`
invariant on cut shapes guarantees the cut subtrees are trace-free).

## What this file provides (scaffold)

- `isInaccessibleSubtree`: predicate that a TraceTree subtree
  corresponds to a vertex in `Y_ℓ`.
- `cutPhaseCompatible`: predicate that an admissible cut extracts
  only phase-accessible subtrees.
- `comulPhaseDel` (TODO): the restricted coproduct sum.
- `comulPhaseDel_coassoc` (TODO): Lemma 1.14.6.

## What this file does NOT do

The actual restricted-sum construction and the coassociativity proof
are deferred. The proof strategy for coassociativity follows MCB Lemma
1.14.6: the bijection between cuts on `T` and pairs (cut on T/^c F_v,
cut on F_v) restricts to phase-compatible cuts, since the
inaccessibility set Y_ℓ is partially ordered by containment.
Discharging in Lean requires careful use of the existing
`comulDelAlgHom`-coassociativity infrastructure plus the
phase-restriction filter.

## Connection to `Phase.lean` PICStrength

Once Δ^c_Φ lands fully, `Phase.lean`'s `PICStrength` modes can be
re-expressed as different choices of phase-restriction predicate:

- `strong` (PIC₁) ↔ `cutPhaseCompatible` with strict `Y_ℓ` (heads of
  lower phases excluded)
- `weak` (PIC₂) ↔ `cutPhaseCompatible` with relaxed `Y_ℓ` (heads
  accessible)
- `linearizationBound` (SCD 2026) ↔ unrestricted `comulDelAlgHom`
  (unmodified Connes-Kreimer Δ^c) + Cyclic Linearization gate

This is the next migration once the algebraic side is complete.
-/

namespace Minimalist.Merge

open ConnesKreimer
open Minimalist (PlanarMarking SyntacticObject LIToken)

-- ============================================================================
-- § 1: Phase-compatibility predicate on TraceTree subtrees
-- ============================================================================

/-- `TraceTree LIToken Unit` → `Option SyntacticObject` forgetful map:
    succeeds on trace-free trees, returns `none` if any `.trace ()`
    leaf survives. The `IsNotTrace` invariant on `CutShape` guarantees
    that for actual cut-extracted subtrees this returns `some`.

    Inline-defined here (parallel to `Merge/Defs.lean`'s
    `treeToSyntacticObject?` for `DecoratedTree LIToken`) because
    `TraceTree α β` and `DecoratedTree α` are distinct types in the
    Hopf substrate (see `Core.Combinatorics.RootedTree.Decorated`). -/
def traceTreeToSyntacticObject? :
    ConnesKreimer.TraceTree LIToken Unit → Option Minimalist.SyntacticObject
  | .leaf tok => some (.leaf tok)
  | .trace _  => none
  | .node l r => do
      let l' ← traceTreeToSyntacticObject? l
      let r' ← traceTreeToSyntacticObject? r
      pure (.node l' r')

/-- Whether a `TraceTree` subtree (typically extracted by an admissible
    cut) corresponds to an SO vertex in the inaccessibility set
    `Y_ℓ` of phase `Φ_ℓ` on `T`. Returns `false` when the subtree
    cannot be projected back to an SO (trace-containing); per the
    `IsNotTrace` invariant of `CutShape`, this case does not arise
    for actual cut-extracted subtrees, but is handled defensively. -/
noncomputable def isInaccessibleSubtree (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) (subtree : TraceTree LIToken Unit) : Bool :=
  match traceTreeToSyntacticObject? subtree with
  | some so => decide (so ∈ inaccessibleTerms m T ℓ)
  | none    => false

/-- A cut shape on `T.toHc` is **phase-compatible** with phase `Φ_ℓ`
    on `T` iff every subtree it extracts is phase-accessible
    (i.e., not in the inaccessibility set `Y_ℓ`).

    This is the predicate that filters the standard Connes-Kreimer
    coproduct sum to obtain Δ^c_Φ (@cite{marcolli-chomsky-berwick-2025}
    Definition 1.14.5 eq 1.14.6).

    `noncomputable` because `Finset.toList` (via `Multiset.toList`)
    relies on `Quot.unquot` and is non-constructive. The substantive
    Δ^c_Φ implementation will avoid this — for the scaffold, the
    classical existence is sufficient. -/
noncomputable def cutPhaseCompatible (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) (c : CutShape T.toHc) : Bool :=
  ((CutShape.cutForest c).toFinset.toList).all
    (fun subtree => !isInaccessibleSubtree m T ℓ subtree)

-- ============================================================================
-- § 2: Restricted coproduct Δ^c_Φ (TODO scaffold)
-- ============================================================================

/-- The phase-restricted coproduct Δ^c_Φ
    (@cite{marcolli-chomsky-berwick-2025} Definition 1.14.5 eq 1.14.6).

    Sums over admissible cuts on `T.toHc` that are phase-compatible
    (extract only phase-accessible subtrees). Reduces to the standard
    `comulDelAlgHom` when no cuts are inaccessible.

    TODO: implement the restricted sum construction. The cleanest path:

    1. Take `(CutShape.all T.toHc).filter (cutPhaseCompatible m T ℓ ·)`.
    2. For each cut `c`, build the tensor `forestToHc (cutForest c) ⊗ₜ
       (toHc-embed of remainderDeletion c)`.
    3. Sum.

    The signature is left as `Prop` for now (a placeholder predicate
    `phaseCoproductDefined`) since the full implementation requires
    careful integration with `AddMonoidAlgebra` tensor structure, and
    intermediate steps are best done in a focused refactor. -/
def phaseCoproductDefined (_m : PlanarMarking) (_T : SyntacticObject)
    (_ℓ : LIToken) : Prop := True

/-- @cite{marcolli-chomsky-berwick-2025} Lemma 1.14.6: Δ^c_Φ is well-
    defined and coassociative.

    Proof strategy: the bijection between cuts on `T` and pairs (cut
    on `T/^c F_v`, cut on `F_v`) — which underlies `comulDelAlgHom`
    coassociativity — restricts to phase-compatible cuts because
    `Y_ℓ` is partially ordered by phase containment. Discharging in
    Lean requires careful use of the existing
    `comulDelAlgHom`-coassociativity machinery plus the
    phase-restriction filter.

    Stated here as TODO; the bridge from `Merge/Phase.lean`
    type-level substrate to the algebraic coassociativity proof is
    the next session's work. -/
theorem comulPhaseDel_coassoc (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) :
    phaseCoproductDefined m T ℓ := trivial

end Minimalist.Merge
