import Linglib.Theories.Syntax.Minimalist.HeadFunction
import Linglib.Theories.Syntax.Minimalist.Merge.Defs

/-!
# Algebraic Phase Theory
@cite{marcolli-chomsky-berwick-2025} §1.14

Implements the MCB algebraic formulation of Phase Theory, building on
the **vertex-keyed head function** `headAtVertex` from `HeadFunction.lean`.

## What MCB §1.14 says

Phase Theory is *defined via the head function*, not stipulated. Given
a head function `h_T` on T, **Lemma 1.14.1** partitions the vertices of T
into projection paths γ_ℓ — one per leaf ℓ — where γ_ℓ is the path
from ℓ up to its **maximal projection** vertex v_ℓ (the highest vertex
w with h_T(w) = ℓ). **Definition 1.14.3** then identifies the **phases**
Φ_ℓ ⊂ T as the accessible terms inside v_ℓ, partitioning the syntactic
object.

The **inaccessibility set** Y_ℓ (eq 1.14.5) is then the set of
accessible terms in the *interior* of any *lower* phase. The **phase
coproduct** Δ^c_Φ (Definition 1.14.5) is the algebraic operator that
extracts only the *accessible* (= non-inaccessible) terms from T —
this is the algebraic implementation of the Phase Impenetrability
Condition. Lemma 1.14.6 proves Δ^c_Φ is well-defined and coassociative.

## Encoding (post Phase 3.B.1 refoundation)

- All vertex-relative head queries route through `HeadFunction.headAtVertex h T w`,
  the substrate primitive landed in Phase 3.A. The T parameter is the
  containing tree (per MCB Def 1.13.3); v is a vertex of T (per the
  `v ∈ T.subtrees` consumer-side hypothesis).
- The body of `headAtVertex h T v` currently descends into v's own planar
  representative (`h.section_.σ v`) rather than searching for v inside
  `h.section_.σ T`. These agree IFF the section is **locally coherent**
  on T (i.e., `h.section_.σ (a*b) ∈ {(h.section_.σ a) * (h.section_.σ b),
  (h.section_.σ b) * (h.section_.σ a)}`). All theorems below are stated
  modulo this coherence hypothesis where required.

## What this file does

- **§1**: Lemma 1.14.1 substrate — `projectionPath`, `maximalProjection`,
  the chain-on-γ theorem (statement; proof requires §1.13.3 coherence).
- **§2**: `phaseHeadLeaves` (L_Φ(T) of Def 1.14.3 eq 1.14.1).
- **§3**: `phaseInterior` (Φ°_ℓ, eq 1.14.3) and `phaseEdge` (∂Φ_ℓ, eq 1.14.4).
- **§4**: `inaccessibleTerms` (Y_ℓ, eq 1.14.5) and `phaseAccessibleAt`.

## Out of scope (queued for Phase 3.C)

- The **algebraic phase coproduct** Δ^c_Φ (Def 1.14.5 eq 1.14.6)
- Coassociativity (Lemma 1.14.6)
- Connection to `PICStrength` (Phase.lean's PIC strength enum)
- `ComplementedHeadFunction` (Def 1.14.2) is in `HeadFunction.lean` (Phase 3.B.2)
-/

namespace Minimalist.Merge

open Minimalist (HeadFunction ComplementedHeadFunction SyntacticObject LIToken)

-- ============================================================================
-- § 1: Maximal Projection Vertex (Lemma 1.14.1)
-- ============================================================================

/-- The projection path γ_ℓ of leaf ℓ in T under head function h
    (@cite{marcolli-chomsky-berwick-2025} Lemma 1.14.1): the multiset of
    vertices `w ∈ V(T)` such that `headAtVertex h T w = ℓ`.

    Per Lemma 1.14.1, this multiset forms a path in T from ℓ up to the
    maximal projection vertex v_ℓ. The path is **trivial** (contains
    only ℓ itself) when ℓ is not the head of any internal vertex of T. -/
noncomputable def projectionPath (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  T.subtrees.filter (fun w => decide (h.headAtVertex T w = ℓ))

/-- **Lemma 1.14.1 (chain property)**: any two vertices on the same
    projection path γ_ℓ are comparable under containment — one contains
    the other.

    @cite{marcolli-chomsky-berwick-2025} Lemma 1.14.1 (book p. 132).
    The "γ_ℓ is a path" claim has two parts:
    (a) **Connectedness**: vertices form a containment-chain (this theorem).
    (b) **Endpoints**: leaf ℓ at the bottom, maximal projection v_ℓ at the top.

    Hypotheses required for Phase 3.C proof:
    - `LocallyCoherent h T`: σ behaves structurally on T's subtrees.
    - `Nodup` on σ T's planar leaves: linguistic well-formedness.

    Proof strategy: vertices `w` with `headAtVertex T w = ℓ` correspond
    to ancestors of `ℓ`'s leaf-position in the planar embedding `σ T`.
    Ancestors of any node form a containment-chain. Discharging via
    `headAtVertex_coherent` (currently sorry'd, see Phase 3.C TODO). -/
theorem projectionPath_chain (h : HeadFunction) (T : SyntacticObject)
    (_hCoh : h.LocallyCoherent T)
    (_hNodup : (leafTokensPlanar (h.section_.σ T)).Nodup)
    (ℓ : LIToken) {w₁ w₂ : SyntacticObject}
    (_h₁ : w₁ ∈ projectionPath h T ℓ) (_h₂ : w₂ ∈ projectionPath h T ℓ) :
    Minimalist.contains w₁ w₂ ∨ Minimalist.contains w₂ w₁ ∨ w₁ = w₂ := by
  -- Phase 3.C TODO: discharge via `headAtVertex_coherent` + planar-descent
  -- argument. Both hypotheses (LocallyCoherent + Nodup) are forwarded to
  -- the substrate theorem.
  sorry

/-- The **maximal projection vertex** v_ℓ of leaf ℓ in T
    (@cite{marcolli-chomsky-berwick-2025} Lemma 1.14.1): the topmost
    vertex on `projectionPath h T ℓ`, ordered by containment.

    Returns `none` if `projectionPath h T ℓ` is empty (ℓ ∉ L(T) under h).
    Otherwise returns the vertex containing all others on γ_ℓ (the unique
    maximal element under containment, well-defined by `projectionPath_chain`).

    Implementation: filter `T.subtrees` to those on γ_ℓ that are NOT
    properly contained in any other γ_ℓ vertex. Returns the first (in
    `Multiset.toList` order) — by `projectionPath_chain` this is unique
    when nonempty. -/
noncomputable def maximalProjection (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Option SyntacticObject :=
  let γ := projectionPath h T ℓ
  let topmost := γ.filter (fun w =>
    decide (∀ w' ∈ γ, w' ≠ w → ¬ Minimalist.contains w' w))
  topmost.toList.head?

/-- A projection path is **non-trivial** (contains at least one
    internal vertex) when its cardinality exceeds 1 — i.e., the leaf has
    ascended at least one level in T. Per Definition 1.14.3, only
    non-trivial projection paths give rise to phases. -/
noncomputable def isNonTrivialProjection (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Bool :=
  decide (1 < (projectionPath h T ℓ).card)

-- ============================================================================
-- § 2: Phase Head Leaves L_Φ(T) (Definition 1.14.3 eq 1.14.1)
-- ============================================================================

/-- The set L(T) of leaves of T as LITokens, under head function `h`.
    Renamed alias for `HeadFunction.leafTokens` matching MCB notation. -/
def leafSet (h : HeadFunction) (T : SyntacticObject) : List LIToken := h.leafTokens T

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.14.3 (eq 1.14.1):
    L_Φ(T) = the set of leaves ℓ ∈ L(T) such that γ_ℓ contains
    interior (non-leaf) vertices. Each such ℓ is the head of a phase. -/
noncomputable def phaseHeadLeaves (h : HeadFunction) (T : SyntacticObject) : List LIToken :=
  (leafSet h T).filter (fun ℓ => isNonTrivialProjection h T ℓ)

-- ============================================================================
-- § 3: Phase Interior Φ°_ℓ and Edge ∂Φ_ℓ (Definitions 1.14.3, 1.14.4)
-- ============================================================================

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.14.3 (eq 1.14.3):
    For ℓ ∈ L_Φ(T) with maximal projection v_ℓ, the **interior** of
    the phase Φ_ℓ is

      Φ°_ℓ := {T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ}}

    — the accessible terms strictly inside the maximal projection.
    Per MCB Remark 1.14.4, this is the part of the phase that becomes
    inaccessible to further computation once a higher phase is built
    via External Merge.

    NB: the "complemented" version of this definition (Def 1.14.3 step 4,
    using the complement Z_v from `ComplementedHeadFunction.complementOf`)
    refines the interior to T_{s_ℓ} (the head's complement-side sister)
    rather than all of T_{v_ℓ}. The simpler T_{v_ℓ} form here is the
    bare-head version; the complemented refinement is Phase 3.B.3 work. -/
noncomputable def phaseInterior (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  match maximalProjection h T ℓ with
  | none    => 0
  | some vℓ =>
    -- Acc'(T): all subtrees of T (per MCB notation)
    -- restricted to those contained in T_{v_ℓ}
    T.subtrees.filter (fun Tv => decide (Minimalist.contains vℓ Tv))

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.14.3 (eq 1.14.4):
    The **edge** ∂Φ_ℓ of phase Φ_ℓ, parameterized over a
    `ComplementedHeadFunction`.

    For ℓ ∈ L_Φ(T) with maximal projection v_ℓ and complement
    `h.complementOf T v_ℓ = some Z_v` (non-empty case): the edge consists
    of accessible terms contained in T_{v_ℓ} but NOT in `Z_v` (the complement
    of the head):

      ∂Φ_ℓ := { T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ} ∧ T_v ⊄ Z_v }

    For `h.complementOf T v_ℓ = none` (exocentric head, no complement):
    ∂Φ_ℓ = Φ_ℓ (the entire phase content is at the edge).

    Note: this signature takes a `ComplementedHeadFunction` (extending
    `HeadFunction` with complement info per MCB Def 1.14.2). For consumers
    holding only a bare `HeadFunction`, lift via
    `ComplementedHeadFunction.leftSpine` (or supply a custom
    `complementOf`). -/
noncomputable def phaseEdgeWith (h : ComplementedHeadFunction)
    (T : SyntacticObject) (ℓ : LIToken) : Multiset SyntacticObject :=
  match maximalProjection h.toHeadFunction T ℓ with
  | none    => 0
  | some vℓ =>
    let phaseContent := T.subtrees.filter
      (fun Tv => decide (Minimalist.contains vℓ Tv))
    match h.complementOf T vℓ with
    | none =>
      -- Empty-complement case: edge = entire phase content
      phaseContent
    | some Zv =>
      -- Non-empty complement: edge = phase content minus Zv-interior
      phaseContent.filter (fun Tv => decide (¬ Minimalist.contains Zv Tv))

/-- Bare `phaseEdge` for `HeadFunction`-only consumers: lifts to the trivial
    `ComplementedHeadFunction` with `complementOf = none` (exocentric).
    Returns the entire phase content per the empty-complement case. -/
noncomputable def phaseEdge (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  phaseEdgeWith ⟨h, fun _ _ => none⟩ T ℓ

-- ============================================================================
-- § 4: Inaccessibility Set Y_ℓ (eq 1.14.5)
-- ============================================================================

/-- The partial order on phases (@cite{marcolli-chomsky-berwick-2025}
    after Definition 1.14.3): Φ_ℓ is a **lower phase** than Φ_ℓ' when
    Φ_ℓ ⊂ Φ_ℓ' as sets of accessible terms. We approximate this by
    interior containment of the maximal projection vertices. -/
noncomputable def isLowerPhaseThan (h : HeadFunction) (T : SyntacticObject)
    (ℓ ℓ' : LIToken) : Bool :=
  match maximalProjection h T ℓ, maximalProjection h T ℓ' with
  | some vℓ, some vℓ' => decide (Minimalist.contains vℓ' vℓ)
  | _, _ => false

/-- @cite{marcolli-chomsky-berwick-2025} eq (1.14.5): the
    **inaccessibility set** Y_ℓ for phase Φ_ℓ:

      Y_ℓ := { T_v ∈ Acc'(T) | T_v ∈ ⋃_{ℓ' < ℓ} Φ°_ℓ' }

    — accessible terms that lie in the interior of any *strictly
    lower* phase. The complement Φ_ℓ ∖ Y_ℓ is the set of terms
    available for computation in phase Φ_ℓ. -/
noncomputable def inaccessibleTerms (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let lowerPhases := (phaseHeadLeaves h T).filter (fun ℓ' => isLowerPhaseThan h T ℓ' ℓ)
  -- Union of interiors of all lower phases (Multiset sum)
  (lowerPhases.map (phaseInterior h T)).foldr (· + ·) 0

/-- The **accessible terms in phase Φ_ℓ**: the phase content minus the
    inaccessibility set. These are the terms available for further
    Merge computation when phase Φ_ℓ is being built or extended.

    This is the set summed over by the algebraic phase coproduct
    Δ^c_Φ (Definition 1.14.5 eq 1.14.6) — the algebraic-side substrate
    is queued for Phase 3.C. -/
noncomputable def phaseAccessibleAt (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let interior := phaseInterior h T ℓ
  let inaccessible := inaccessibleTerms h T ℓ
  interior.filter (fun Tv => decide (Tv ∉ inaccessible))

end Minimalist.Merge
