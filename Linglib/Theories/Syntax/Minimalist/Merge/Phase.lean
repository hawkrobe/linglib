import Linglib.Theories.Syntax.Minimalist.HeadFunction
import Linglib.Theories.Syntax.Minimalist.Merge.Defs

/-!
# Algebraic Phase Theory
@cite{marcolli-chomsky-berwick-2025} §1.14

Implements the MCB algebraic formulation of Phase Theory, building on
the per-vertex head function from `HeadFunction.lean`.

## What MCB §1.14 says

Phase Theory is *defined via the head function*, not stipulated. Given
a head function `h_T` on T, Lemma 1.14.1 partitions the vertices of T
into projection paths γ_ℓ — one per leaf ℓ — where γ_ℓ is the path
from ℓ up to its **maximal projection** vertex v_ℓ (the highest vertex
w with h_T(w) = ℓ). Definition 1.14.3 then identifies the **phases**
Φ_ℓ ⊂ T as the accessible terms inside v_ℓ, partitioning the syntactic
object.

The **inaccessibility set** Y_ℓ (eq 1.14.5) is then the set of
accessible terms in the *interior* of any *lower* phase. The **phase
coproduct** Δ^c_Φ (Definition 1.14.5) is the algebraic operator that
extracts only the *accessible* (= non-inaccessible) terms from T —
this is the algebraic implementation of the Phase Impenetrability
Condition.

Lemma 1.14.6 proves Δ^c_Φ is well-defined and coassociative.

## What this file does

Lands the type-level substrate:

- `maximalProjectionVertex` (the v_ℓ of Lemma 1.14.1)
- `projectionPath` (the γ_ℓ of Lemma 1.14.1)
- `phaseHeadLeaves` (the L_Φ(T) of Definition 1.14.3 — leaves whose
  γ_ℓ contains internal vertices)
- `phaseInterior` (Φ°_ℓ, eq 1.14.3)
- `phaseEdge` (∂Φ_ℓ, eq 1.14.4 — when the complement is nonempty)
- `inaccessibleTerms` (Y_ℓ, eq 1.14.5)
- `phaseAccessibleAt` (the set Φ_ℓ ∖ Y_ℓ of terms available for
  computation in phase Φ_ℓ)

## What this file does NOT do (yet)

The **algebraic phase coproduct** Δ^c_Φ (Definition 1.14.5 eq 1.14.6)
is not yet implemented. Doing so requires integration with the existing
ConnesKreimer Hopf substrate (`Core/Algebra/ConnesKreimer/Coproduct.lean`)
to express the modified-coproduct equation:

  Δ^c_Φ(T) = Σ_{v ∈ Φ_{h_T} ∖ Y_{h_T}} F_v ⊗ T/^c F_v

This is queued as a follow-up — the type-level substrate landed here
gives the inaccessibility set used to *select* terms for the
coproduct.

## Connection to existing `Phase.lean`

The existing `Phase.lean` provides a structural `Phase` record
(head/complement/edge as data) with `PICStrength` enum modes. Once the
algebraic Δ^c_Φ lands, those modes can be re-expressed as which
coproduct (and which Y_ℓ restriction) is used:

- `strong` (PIC₁) ↔ Δ^c_Φ with Y_ℓ excluding heads of lower phases
- `weak` (PIC₂) ↔ Δ^c_Φ with relaxed Y_ℓ (heads accessible)
- `linearizationBound` ↔ unrestricted Δ^c + Cyclic Linearization gate
  (per @cite{sande-clem-dabkowski-2026} §6.2)

That refactor is queued as a follow-up to Δ^c_Φ.
-/

namespace Minimalist.Merge

open Minimalist (PlanarMarking SyntacticObject LIToken)

-- ============================================================================
-- § 1: Maximal Projection Vertex (Lemma 1.14.1)
-- ============================================================================

/-- The projection path γ_ℓ of leaf ℓ in T under marking m
    (@cite{marcolli-chomsky-berwick-2025} Lemma 1.14.1): the set of
    vertices `w` of T such that `headAt m w = ℓ`.

    Per Lemma 1.14.1, this set is a path in T from ℓ up to the
    maximal projection vertex v_ℓ. The path is "trivial" (contains
    only ℓ itself) if ℓ is not the head of any internal vertex. -/
def projectionPath (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) : List SyntacticObject :=
  T.subtrees.filter (fun w => decide (m.headAt w = ℓ))

/-- The **maximal projection vertex** v_ℓ of leaf ℓ in T
    (@cite{marcolli-chomsky-berwick-2025} Lemma 1.14.1): the topmost
    vertex on `projectionPath m T ℓ`. Returns `none` if ℓ is not in T
    (or, more precisely, has empty projection path).

    Since `subtrees` enumerates T in top-down order, the first
    element of the filtered path is the highest vertex. -/
def maximalProjectionVertex (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) : Option SyntacticObject :=
  (projectionPath m T ℓ).head?

/-- A projection path is **non-trivial** (contains at least one
    internal vertex) when its length exceeds 1 — i.e., the leaf has
    ascended at least one level. Per Definition 1.14.3, only
    non-trivial projection paths give rise to phases. -/
def isNonTrivialProjection (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) : Bool :=
  decide (1 < (projectionPath m T ℓ).length)

-- ============================================================================
-- § 2: Phase Head Leaves L_Φ(T) (Definition 1.14.3)
-- ============================================================================

/-- The set L(T) of leaves of T as LITokens. Renamed alias for
    `SyntacticObject.leafTokens`, matching MCB notation. -/
abbrev leafSet (T : SyntacticObject) : List LIToken := T.leafTokens

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.14.3 (eq 1.14.1):
    L_Φ(T) = the set of leaves ℓ ∈ L(T) such that γ_ℓ contains
    interior (non-leaf) vertices. Each such ℓ is the head of a phase. -/
def phaseHeadLeaves (m : PlanarMarking) (T : SyntacticObject) : List LIToken :=
  (leafSet T).filter (fun ℓ => isNonTrivialProjection m T ℓ)

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
    via External Merge. -/
def phaseInterior (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) : List SyntacticObject :=
  match maximalProjectionVertex m T ℓ with
  | none    => []
  | some vℓ =>
    -- Acc'(T): all subtrees of T (per MCB notation)
    -- restricted to those contained in T_{v_ℓ}
    T.subtrees.filter (fun Tv => decide (Minimalist.contains vℓ Tv))

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.14.3 (eq 1.14.4):
    The **edge** ∂Φ_ℓ of phase Φ_ℓ consists of accessible terms
    contained in the sister of the head's mother but not in the
    interior. Per MCB Remark 1.14.4 these remain accessible for
    further computation in higher phases.

    NB: the formal definition (1.14.4) takes the form

      ∂Φ_ℓ := { T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ} ∧ T_w ⊄ T_{s_ℓ} }

    where s_ℓ is the sister of ℓ under the mother of v_ℓ. The current
    implementation provides a simplified placeholder; full handling
    requires the sister-vertex lookup which currently lives elsewhere
    in linglib. -/
def phaseEdge (m : PlanarMarking) (T : SyntacticObject)
    (_ℓ : LIToken) : List SyntacticObject :=
  -- TODO: implement using sister-vertex lookup. The structural shape
  -- is (interior of T_{v_ℓ}) minus (interior of T_{s_ℓ}).
  []

-- ============================================================================
-- § 4: Inaccessibility Set Y_ℓ (eq 1.14.5)
-- ============================================================================

/-- The partial order on phases (@cite{marcolli-chomsky-berwick-2025}
    after Definition 1.14.3): Φ_ℓ is a **lower phase** than Φ_ℓ' when
    Φ_ℓ ⊂ Φ_ℓ' as sets of accessible terms. We approximate this by
    interior containment of the maximal projection vertices. -/
def isLowerPhaseThan (m : PlanarMarking) (T : SyntacticObject)
    (ℓ ℓ' : LIToken) : Bool :=
  match maximalProjectionVertex m T ℓ, maximalProjectionVertex m T ℓ' with
  | some vℓ, some vℓ' => decide (Minimalist.contains vℓ' vℓ)
  | _, _ => false

/-- @cite{marcolli-chomsky-berwick-2025} eq (1.14.5): the
    **inaccessibility set** Y_ℓ for phase Φ_ℓ:

      Y_ℓ := { T_v ∈ Acc'(T) | T_v ∈ ⋃_{ℓ' < ℓ} Φ°_ℓ' }

    — accessible terms that lie in the interior of any *strictly
    lower* phase. The complement Φ_ℓ ∖ Y_ℓ is the set of terms
    available for computation in phase Φ_ℓ. -/
def inaccessibleTerms (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) : List SyntacticObject :=
  let lowerPhases := (phaseHeadLeaves m T).filter (fun ℓ' => isLowerPhaseThan m T ℓ' ℓ)
  -- Union of interiors of all lower phases
  lowerPhases.flatMap (phaseInterior m T)

/-- The **accessible terms in phase Φ_ℓ**: the phase content minus the
    inaccessibility set. These are the terms available for further
    Merge computation when phase Φ_ℓ is being built or extended.

    This is the set summed over by the algebraic phase coproduct
    Δ^c_Φ (Definition 1.14.5 eq 1.14.6) — when the algebraic-side
    substrate lands. -/
def phaseAccessibleAt (m : PlanarMarking) (T : SyntacticObject)
    (ℓ : LIToken) : List SyntacticObject :=
  let interior := phaseInterior m T ℓ
  let inaccessible := inaccessibleTerms m T ℓ
  interior.filter (fun Tv => decide (Tv ∉ inaccessible))

-- ============================================================================
-- § 5: TODO — Algebraic Phase Coproduct Δ^c_Φ (Definition 1.14.5 eq 1.14.6)
-- ============================================================================

/-! The algebraic phase coproduct

      Δ^c_Φ(T) = Σ_{v ∈ Φ_{h_T} ∖ Y_{h_T}} F_v ⊗ T/^c F_v

    is the modified Hopf-algebra coproduct restricted to phase-
    accessible terms. It depends on:

    1. The existing `comulDelAlgHom` from `Core/Algebra/ConnesKreimer/Coproduct.lean`
       (the standard coproduct Δ^c that sums over *all* admissible cuts)
    2. A restriction operator that drops terms in the inaccessibility set Y_ℓ

    The natural construction is:

      Δ^c_Φ T := comulDelAlgHom T |>.filter (admissible_cut_in_phase ℓ)

    where the filter keeps only those tensor terms whose left
    component F_v has root vertex outside Y_ℓ.

    This requires:
    - A `compatible_with_phase : ConnesKreimer.AdmissibleCut → Bool` predicate
    - A coassociativity proof for the restricted coproduct (Lemma 1.14.6)

    Queued. The type-level substrate above suffices to begin the migration
    of `Phase.lean`'s `PICStrength` modes; the algebraic coproduct is
    needed to actually *prove* the consequences (e.g., that
    `PICStrength.strong` extraction is blocked by Δ^c_Φ).
-/

end Minimalist.Merge
