import Linglib.Syntax.Minimalist.Merge.Phase
import Linglib.Syntax.Minimalist.Merge.Defs
import Linglib.Syntax.Minimalist.Phase
import Linglib.Core.Algebra.ConnesKreimer.Coproduct

/-!
# Algebraic Phase Coproduct Δ^c_Φ
[marcolli-chomsky-berwick-2025] §1.14, Definition 1.14.5

Implements the **phase-restricted coproduct** Δ^c_Φ of MCB §1.14, eq (1.14.6):

    Δ^c_Φ(T) = Σ_{v ∈ Φ_{h_T} ∖ Y_{h_T}}  F_v ⊗ T/^c F_v

where the sum is restricted to vertices `v` that are **phase-accessible** —
not in the inaccessibility set `Y_ℓ` of any lower phase. This is the
algebraic implementation of the Phase Impenetrability Condition: cuts
that would extract material from a closed lower phase are dropped from
the coproduct.

Per MCB Lemma 1.14.6 (book p. 138), Δ^c_Φ is well-defined and coassociative.

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
`Y_ℓ`. We use the `traceTreeToSyntacticObject?` partial inverse
(returning `none` for trace-containing trees, but the `IsNotTrace`
invariant on cut shapes guarantees the cut subtrees are trace-free).

## What this file provides (Phase 3.C)

- `traceTreeToSyntacticObject?`: forgetful map from TraceTree to SO.
- `isInaccessibleSubtree`: predicate that a TraceTree subtree
  corresponds to a vertex in `Y_ℓ`.
- `cutPhaseCompatible`: predicate that an admissible cut extracts
  only phase-accessible subtrees.
- `comulPhaseC`: tree-level Δ^c_Φ as a filtered sum of cuts on `T.toHc`,
  returning a value in `Hc ℤ LIToken ⊗[ℤ] Hc ℤ LIToken`.
- `comulPhaseC_coassoc` (sorry'd): Lemma 1.14.6 coassociativity.

## Δ^c vs Δ^d — convention note

MCB Definition 1.14.5 (book p. 138) explicitly uses `Δ^ω with ω = c`
(the contraction coproduct). Our implementation follows MCB faithfully:
the right channel uses `forestToHc {remainder c}` (single tree, contraction
preserves the leaf vertex with a trace label), NOT `deletionRightChannel`
(which would correspond to Δ^d).

The standard `comulAlgHom : Hc →ₐ[R] Hc ⊗[R] Hc` (in `ConnesKreimer/Coproduct.lean`)
is the unrestricted Δ^c. The Bialgebra typeclass uses Δ^c (via `instBialgebraHc`
in `Bialgebra.lean`); Δ^c is the proven coassociative coproduct (Lemma 1.2.10).

## Coassociativity proof strategy (Lemma 1.14.6)

Per MCB book p. 138, Δ^c_Φ's coassociativity is proved NOT directly but via
**bijection with Δ^c on a cut tree**:

> The terms in Δ^c_Φ(T) can be bijectively mapped to the terms in Δ^c(T/^c π_C(T)),
> where π_C(T) is the admissible cut that cuts each edge above each vertex s_ℓ.
> The bijection consists of replacing the labels F̄_{v_i} at the new leaves of
> T/^c π_C(T) with the restored T_{s_ℓ}. Thus the coassociativity identity for
> Δ^c (Lemma 1.2.10) gives the coassociativity identity for Δ^c_Φ.

In Lean: since `comulAlgHom_coassoc` (`comul_coassoc` in `Bialgebra.lean`) is
proven for Δ^c, the bijection-pushforward gives Δ^c_Φ's coassociativity.
Discharging the bijection in Lean is the substantive remaining work.

## Workspace extension (LinearMap version)

For workspaces F = ⊔_a T_a, MCB Def 1.14.5 sets Δ^c_Φ(F) = ⊔_a Δ^c_Φ(T_a)
(multiplicative extension, each tree using its own phase context). The
`LinearMap`-shaped lift `Hc → Hc ⊗ Hc` requires per-tree phase context lookup,
which is non-trivial to encode (the tree alone doesn't carry SO context).

Phase 3.C provides the **tree-level** value `comulPhaseC` returning
`Hc ⊗ Hc`. The full `LinearMap` extension over arbitrary workspaces is
deferred — it's mathematically natural but requires an SO-recovery layer
(`traceTreeToSyntacticObject?` is partial; full encoding needs Phase 3.D
infrastructure for SO ↔ TraceTree round-trip on phase-restricted contexts).

## Connection to `Phase.lean` PICStrength

The `PICStrength` modes (`.strong | .weak | .linearizationBound`) in `Phase.lean`
are dispatched here:

- `.strong` (PIC₁) ↔ `comulPhaseC` with strict `Y_ℓ` (heads of lower phases excluded)
- `.weak` (PIC₂) ↔ `comulPhaseC` with relaxed `Y_ℓ` (phase-heads accessible)
- `.linearizationBound` (SCD 2026) ↔ `comulAlgHom` (unrestricted Δ^c) +
  Cyclic Linearization gate enforced separately

See §4 below.
-/

namespace Minimalist.Merge

open ConnesKreimer
open scoped TensorProduct
open Minimalist (HeadFunction ComplementedHeadFunction SyntacticObject LIToken PICStrength)

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
noncomputable def isInaccessibleSubtree (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) (subtree : TraceTree LIToken Unit) : Bool :=
  match traceTreeToSyntacticObject? subtree with
  | some so => decide (so ∈ inaccessibleTerms h T ℓ)
  | none    => false

/-- A cut shape on `T.toHc` is **phase-compatible** with phase `Φ_ℓ`
    on `T` iff every subtree it extracts is phase-accessible
    (i.e., not in the inaccessibility set `Y_ℓ`).

    This is the predicate that filters the standard Connes-Kreimer
    coproduct sum to obtain Δ^c_Φ ([marcolli-chomsky-berwick-2025]
    Definition 1.14.5 eq 1.14.6).

    `noncomputable` because `Finset.toList` (via `Multiset.toList`)
    relies on `Quot.unquot` and is non-constructive. The substantive
    Δ^c_Φ implementation here is for definitional clarity; the
    classical existence of the predicate is sufficient for stating
    the algebraic lemmas. -/
noncomputable def cutPhaseCompatible (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) (c : CutShape T.toHc) : Bool :=
  ((CutShape.cutForest c).toFinset.toList).all
    (fun subtree => !isInaccessibleSubtree h T ℓ subtree)

-- ============================================================================
-- § 2: Tree-level Δ^c_Φ (MCB Def 1.14.5 eq 1.14.6)
-- ============================================================================

/-- The **tree-level phase coproduct** Δ^c_Φ
    ([marcolli-chomsky-berwick-2025] Definition 1.14.5 eq 1.14.6),
    using the contraction coproduct shape (Δ^c, with `remainder` rather than
    `remainderDeletion`).

    **Implementation**: routes through `comulTreeFiltered` (in
    `ConnesKreimer/Coproduct.lean`), the shared filtered-coproduct primitive
    that also defines `comulTree` (with `fun _ => true`). The phase-restricted
    case uses `cutPhaseCompatible h T ℓ` as the filter.

    Sums over admissible cuts `c : CutShape T.toHc` on the planar embedding
    of `T` that are phase-compatible (extract only phase-accessible subtrees
    per `cutPhaseCompatible`). Includes the explicit `T ⊗ 1` primitive term;
    the empty cut contributes the `1 ⊗ T` term.

    Compared to the standard `comulTree` (in `ConnesKreimer/Coproduct.lean`),
    this version drops cuts that extract subtrees in `Y_ℓ` (the inaccessibility
    set of lower phases). The unrestricted-limit recovery is provable by
    `comulPhaseC_eq_comulTree_of_no_filter` below. -/
noncomputable def comulPhaseC (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) :
    Hc ℤ LIToken ⊗[ℤ] Hc ℤ LIToken :=
  comulTreeFiltered T.toHc (cutPhaseCompatible h T ℓ)

/-- **Unrestricted-limit recovery**: when no cuts are phase-incompatible
    (the filter is constantly true), Δ^c_Φ recovers the standard Δ^c.
    Substantive content of "Δ^c_Φ is a *restriction* of Δ^c, not a parallel
    definition" — provable as a one-liner via the shared `comulTreeFiltered`
    primitive. -/
theorem comulPhaseC_eq_comulTree_of_no_filter
    (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken)
    (hAll : ∀ c : CutShape T.toHc, cutPhaseCompatible h T ℓ c = true) :
    comulPhaseC h T ℓ = comulTree T.toHc := by
  unfold comulPhaseC comulTree comulTreeFiltered
  congr 1
  apply Finset.sum_congr (Finset.ext (fun c => by simp [hAll c]))
  intros; rfl

/-- Standard `comulTree T.toHc` (= unrestricted Δ^c on T's planar embedding)
    in the same shape as `comulPhaseC`. The unfiltered sum form. Useful for
    comparison and the `linearizationBound` PIC mode. -/
noncomputable def comulC_unrestricted (T : SyntacticObject) :
    Hc ℤ LIToken ⊗[ℤ] Hc ℤ LIToken :=
  comulTree T.toHc

-- ============================================================================
-- § 3: Coassociativity (MCB Lemma 1.14.6) — DEFERRED to Phase 3.E
-- ============================================================================

/-! ### Coassociativity status

The headline algebraic theorem MCB Lemma 1.14.6 — `(Δ^c_Φ ⊗ id) ∘ Δ^c_Φ =
(id ⊗ Δ^c_Φ) ∘ Δ^c_Φ` — is **not stated here**. Stating it requires a
`LinearMap`-shaped Δ^c_Φ to express the iterated composition; the current
`comulPhaseC` returns `Hc ⊗ Hc` directly (single tree, no per-channel
recursion). The LinearMap extension is non-trivial because the per-tree
phase context (h, T, ℓ) doesn't propagate to extracted sub-trees in a
canonical way (each sub-tree has its own phase configuration).

**Proof strategy when LinearMap version lands** (MCB book p. 138):
1. Define `cutAtPhaseHeadEdges T h ℓ : CutShape T.toHc` — the canonical
   admissible cut that severs every phase-head edge.
2. Show `comulPhaseC h T ℓ` corresponds to `comulTree (T.toHc / cutAtPhaseHeadEdges)`
   under a label-renaming bijection that relabels the new leaves with their
   `T_{s_ℓ}` originals.
3. Apply `comul_coassoc` (`ConnesKreimer/Bialgebra.lean`) on the cut tree;
   pushforward through the bijection gives Δ^c_Φ coassoc.

Phase 3.E will land the LinearMap extension and discharge the bijection.
The current substrate is sufficient for downstream tree-level reasoning.
-/

-- ============================================================================
-- § 4: PICStrength dispatch (weak PIC properly wired)
-- ============================================================================

/-- The **inaccessibility set `Y_ℓ` under WEAK PIC**: relaxed version of
    `inaccessibleTerms` where heads of lower phases remain accessible
    (only the rest of their interior is closed).

    Per [marcolli-chomsky-berwick-2025] Remark 1.14.4 (book p. 136):
    "There are reasons in the current theory of Merge for excluding head
    movement, which would indicate that the head itself would also not
    remain accessible. A more restrictive Phase Theory would then also
    include the heads of the lower phases in the set Y_ℓ."

    The DEFAULT (`inaccessibleTerms`) IS the strict version. The WEAK
    version excludes the head leaves of lower phases from Y_ℓ:

      Y_ℓ_weak := Y_ℓ ∖ {h_{T_{v_ℓ'}} : ℓ' < ℓ}

    where `h_{T_{v_ℓ'}}` is the head leaf of lower phase ℓ'. -/
noncomputable def inaccessibleTerms_weak (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let strict := inaccessibleTerms h T ℓ
  let phaseHeadSOs : Multiset SyntacticObject :=
    (phaseHeadLeaves h T).filter (fun ℓ' => isLowerPhaseThan h T ℓ' ℓ)
      |>.map (fun ℓ' => SyntacticObject.leaf ℓ')
      |> List.toFinset |>.val
  strict.filter (fun Tv => decide (Tv ∉ phaseHeadSOs))

/-- WEAK-PIC analog of `cutPhaseCompatible`: a cut is **weak-phase-compatible**
    when every extracted subtree is in the WEAK accessible set
    (`inaccessibleTerms_weak` allows phase-heads to remain accessible). -/
noncomputable def cutPhaseCompatible_weak (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) (c : CutShape T.toHc) : Bool :=
  ((CutShape.cutForest c).toFinset.toList).all
    (fun subtree => match traceTreeToSyntacticObject? subtree with
      | some so => decide (so ∉ inaccessibleTerms_weak h T ℓ)
      | none    => true)

/-- The **WEAK** tree-level phase coproduct Δ^c_Φ_weak: filtered with
    `cutPhaseCompatible_weak` (phase heads remain accessible). -/
noncomputable def comulPhaseC_weak (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) :
    Hc ℤ LIToken ⊗[ℤ] Hc ℤ LIToken :=
  comulTreeFiltered T.toHc (cutPhaseCompatible_weak h T ℓ)

/-- The phase-coproduct under PICStrength dispatch. Selects between the
    strict, weak, and linearization-bound variants per `Phase.lean`'s
    `PICStrength` enum.

    - `.strong`: standard Δ^c_Φ with strict `Y_ℓ` (`comulPhaseC`).
    - `.weak`: Δ^c_Φ with relaxed `Y_ℓ_weak` (`comulPhaseC_weak`); phase-heads
      accessible per [marcolli-chomsky-berwick-2025] Remark 1.14.4.
    - `.linearizationBound`: unrestricted Δ^c (no phase filtering); the
      linearization gate is enforced separately at the externalization layer. -/
noncomputable def comulPICStrength (mode : PICStrength)
    (h : HeadFunction) (T : SyntacticObject) (ℓ : LIToken) :
    Hc ℤ LIToken ⊗[ℤ] Hc ℤ LIToken :=
  match mode with
  | .strong              => comulPhaseC h T ℓ
  | .weak                => comulPhaseC_weak h T ℓ
  | .linearizationBound  => comulC_unrestricted T

end Minimalist.Merge
