import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# Late Merger
@cite{lebeaux-1988} @cite{takahashi-hulsey-2009} @cite{bhatt-pancheva-2004}

Late merger (originally @cite{lebeaux-1988} for adjuncts; extended to NP
restrictors as Wholesale Late Merger by @cite{takahashi-hulsey-2009};
extended to degree clauses by @cite{bhatt-pancheva-2004}) introduces
some sub-constituent of a moved phrase countercyclically at a non-base
position on the movement chain.

## Generic shape

Late merger comes in flavors that differ only in *which positions are
admissible targets* for late merger:

- WLM (NP restrictors): admissible iff case can be assigned there.
- B&P (degree clauses): admissible iff the position can host a ⟨t⟩-scope
  for the degree quantifier (subject to the Heim-Kennedy Constraint).
- Lebeaux (adjuncts): admissible everywhere on the chain.

The Condition C bleeding profile is the same in every flavor: late
merger bleeds Condition C iff there exists an *admissible* chain
position strictly above the pronoun binder. We factor this shared
shape into the polymorphic `lateMergerBleeds` operation, with
`wlmBleedsCondC` as the case-licensing specialization for NPs.

## Core ideas

Under the copy theory of movement, a moved phrase leaves copies at
every position on its chain. Late merger allows the relevant
sub-constituent to be introduced at *any* copy position, subject to
the flavor's admissibility constraint.

If the late-merged constituent contains an R-expression that would be
c-commanded by a coreferential pronoun at the base position, full
reconstruction triggers a Condition C violation. Late merger can
avoid this by introducing the constituent at a higher *admissible*
copy position.

@cite{gong-2022} shows that for NP restrictors the case requirement is
the key factor controlling Condition C reconstruction effects in
Mongolian scrambling: reconstruction tracks case positions, not the
A/A-bar distinction.

## Definitions

- `lateMergerBleeds` — generic late-merger bleeding test, polymorphic
  in position type and admissibility predicate
- `ChainPosition` — a position on a movement chain with its height and
  case availability
- `wlmBleedsCondC` — case-licensing specialization for NP restrictors
- `wlmForcesReconstruction` — negation of `wlmBleedsCondC`
-/

namespace Minimalism

-- ============================================================================
-- S 1: Generic Late-Merger Bleeding
-- ============================================================================

/-- Generic late-merger bleeding test.

    Given a movement chain (any list of positions), a height projection,
    an admissibility predicate, and a binder height: late merger bleeds
    Condition C iff there exists an *admissible* chain position strictly
    above the binder.

    Specializations:
    - `wlmBleedsCondC` (@cite{takahashi-hulsey-2009}): NP restrictors,
      admissible := case-available
    - Late merger of degree clauses (@cite{bhatt-pancheva-2004}): degree
      clauses, admissible := position can host a ⟨t⟩-scope subject to
      the Heim-Kennedy Constraint -/
def lateMergerBleeds {α : Type*} (admissible : α → Bool) (height : α → Nat)
    (chain : List α) (binderHeight : Nat) : Bool :=
  chain.any (fun p => admissible p && height p > binderHeight)

/-- Adding a chain position never removes late-merger bleeding. -/
theorem lateMerger_bleeding_monotone {α : Type*}
    (admissible : α → Bool) (height : α → Nat)
    (chain : List α) (p : α) (binderHeight : Nat)
    (h : lateMergerBleeds admissible height chain binderHeight = true) :
    lateMergerBleeds admissible height (p :: chain) binderHeight = true := by
  simp only [lateMergerBleeds, List.any_cons, Bool.or_eq_true]
  right; exact h

/-- Consing an admissible position above the binder guarantees bleeding. -/
theorem admissible_above_binder_bleeds {α : Type*}
    (admissible : α → Bool) (height : α → Nat)
    (chain : List α) (p : α) (binderHeight : Nat)
    (hadm : admissible p = true) (hgt : height p > binderHeight) :
    lateMergerBleeds admissible height (p :: chain) binderHeight = true := by
  simp only [lateMergerBleeds, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
             decide_eq_true_eq]
  left; exact ⟨hadm, hgt⟩

/-- If every chain position is at or below the binder, late merger
    cannot bleed Condition C — regardless of which admissibility
    predicate is used. -/
theorem top_binder_no_bleed {α : Type*}
    (admissible : α → Bool) (height : α → Nat)
    (chain : List α) (binderHeight : Nat)
    (h : ∀ p ∈ chain, height p ≤ binderHeight) :
    lateMergerBleeds admissible height chain binderHeight = false := by
  simp only [lateMergerBleeds]
  rw [List.any_eq_false]
  intro p hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨_, hgt⟩
  exact absurd hgt (Nat.not_lt.mpr (h p hmem))

/-- If no chain position is admissible, late merger cannot bleed. -/
theorem no_admissible_no_bleed {α : Type*}
    (admissible : α → Bool) (height : α → Nat)
    (chain : List α) (binderHeight : Nat)
    (h : ∀ p ∈ chain, admissible p = false) :
    lateMergerBleeds admissible height chain binderHeight = false := by
  simp only [lateMergerBleeds]
  rw [List.any_eq_false]
  intro p hmem
  simp [h p hmem]

-- ============================================================================
-- S 2: Chain Positions for NP Late Merger
-- ============================================================================

/-- A position on a movement chain.
    `height` encodes structural position (higher = larger Nat).
    `caseAvailable` records whether case can be assigned at this position
    (i.e., whether the Case Filter can be satisfied here). -/
structure ChainPosition where
  height : Nat
  caseAvailable : Bool
  deriving DecidableEq, Repr

-- ============================================================================
-- S 3: WLM (NP Restrictors) and Condition C
-- ============================================================================

/-- Wholesale late merger bleeds Condition C iff there exists a position
    on the movement chain that is (a) strictly above the pronoun binder
    and (b) a position where case can be assigned.

    Case-licensing specialization of `lateMergerBleeds`.

    @cite{gong-2022} condition (2): WLM may bleed Condition C if the
    movement chain permits a case position higher than the pronoun
    binder. -/
def wlmBleedsCondC (chain : List ChainPosition) (binderHeight : Nat) : Bool :=
  lateMergerBleeds (·.caseAvailable) ChainPosition.height chain binderHeight

/-- WLM forces Condition C reconstruction when no case position
    on the chain is above the binder. The NP restrictor must merge
    at its base position (or at least below the binder), placing the
    R-expression within the binder's c-command domain. -/
def wlmForcesReconstruction (chain : List ChainPosition) (binderHeight : Nat) : Bool :=
  !wlmBleedsCondC chain binderHeight

/-- PP-scrambling never benefits from WLM: PPs do not contain a
    determiner with an NP restrictor that can be late-merged.
    PP-scrambling always exhibits obligatory Condition C reconstruction.

    @cite{gong-2022} section 6.2: scrambling of PPs headed by *esreg*
    'against' always forces reconstruction, regardless of the binder's
    position. -/
def ppAlwaysReconstructs : Bool := true

-- ============================================================================
-- S 4: WLM Structural Properties (specializations of generic lemmas)
-- ============================================================================

/-- If every chain position is at or below the binder, WLM forces
    reconstruction. Specialization of `top_binder_no_bleed`. -/
theorem top_binder_forces_reconstruction
    (chain : List ChainPosition) (binderHeight : Nat)
    (h : ∀ cp ∈ chain, cp.height ≤ binderHeight) :
    wlmForcesReconstruction chain binderHeight = true := by
  simp [wlmForcesReconstruction, wlmBleedsCondC,
        top_binder_no_bleed _ ChainPosition.height chain binderHeight h]

/-- A case position above the binder guarantees WLM bleeds Condition C.
    Specialization of `admissible_above_binder_bleeds`. -/
theorem case_above_binder_bleeds
    (chain : List ChainPosition) (binderHeight h : Nat)
    (hgt : h > binderHeight) :
    wlmBleedsCondC (⟨h, true⟩ :: chain) binderHeight = true :=
  admissible_above_binder_bleeds _ _ chain ⟨h, true⟩ binderHeight rfl hgt

/-- WLM bleeding is monotone: adding positions never removes it.
    Specialization of `lateMerger_bleeding_monotone`. -/
theorem wlm_bleeding_monotone
    (chain : List ChainPosition) (cp : ChainPosition) (binderHeight : Nat)
    (h : wlmBleedsCondC chain binderHeight = true) :
    wlmBleedsCondC (cp :: chain) binderHeight = true :=
  lateMerger_bleeding_monotone _ _ chain cp binderHeight h

/-- If no chain position has case available, WLM forces reconstruction
    regardless of heights. Specialization of `no_admissible_no_bleed`. -/
theorem no_case_forces_reconstruction
    (chain : List ChainPosition) (binderHeight : Nat)
    (h : ∀ cp ∈ chain, cp.caseAvailable = false) :
    wlmForcesReconstruction chain binderHeight = true := by
  simp [wlmForcesReconstruction, wlmBleedsCondC,
        no_admissible_no_bleed (·.caseAvailable) ChainPosition.height
          chain binderHeight h]

-- ============================================================================
-- S 5: Condition C over Syntactic Objects
-- ============================================================================

/-- Condition C violation check: does the binder c-command the
    R-expression in tree `root`?

    This is the structural condition checked on concrete
    `SyntacticObject` trees, complementing the abstract chain-position
    analysis in `wlmForcesReconstruction`. -/
def conditionCViolation (root binder rExpr : SyntacticObject) : Bool :=
  cCommandsInB root binder rExpr

/-- Condition C is satisfied in a tree: the binder does NOT c-command
    the R-expression. Takes the tree after any WLM has applied.
    Returns `true` when the R-expression is free. -/
def conditionCSatisfied (tree binder rExpr : SyntacticObject) : Bool :=
  !conditionCViolation tree binder rExpr

-- ============================================================================
-- S 6: Successive-Cyclic Movement and Phase Edges
-- ============================================================================

/-- A position at a phase edge on a movement chain.

    Successive-cyclic movement creates an intermediate copy at each
    phase edge the mover passes through (@cite{chomsky-2000}).
    Whether case is available at the edge determines whether WLM
    can target that position (@cite{gong-2022}). -/
structure PhaseEdgePosition where
  phaseCat : Cat
  height : Nat
  caseAvailable : Bool
  deriving DecidableEq, Repr

/-- Convert a phase edge position to a chain position for WLM. -/
def PhaseEdgePosition.toChainPosition (p : PhaseEdgePosition) : ChainPosition :=
  ⟨p.height, p.caseAvailable⟩

/-- Derive chain positions from successive-cyclic movement through
    phase edges. Each phase edge the mover passes through becomes a
    position on the movement chain. -/
def successiveCyclicChain (edges : List PhaseEdgePosition) : List ChainPosition :=
  edges.map PhaseEdgePosition.toChainPosition

/-- CP edges do not provide case positions. C does not assign structural
    case; it passes tense/agreement features to T via Feature Inheritance
    (@cite{chomsky-2008}). -/
theorem cp_edge_no_case (h : Nat) :
    (PhaseEdgePosition.mk .C h false).toChainPosition.caseAvailable = false := rfl

/-- LDS chain template: movement from an embedded clause through the
    CP edge to a matrix clause position. The CP edge provides no case,
    but the matrix position may — depending on case competitors.

    This is the structural template for @cite{gong-2022}'s LDS data:
    embedded ACC object → Spec,CP (no case) → matrix clause (case
    depends on whether a dependent case competitor exists). -/
def ldsChainTemplate (cpEdgeHeight matrixHeight : Nat) (matrixCaseAvailable : Bool)
    : List ChainPosition :=
  successiveCyclicChain [
    ⟨.C, cpEdgeHeight, false⟩,
    ⟨.v, matrixHeight, matrixCaseAvailable⟩
  ]

/-- A CP edge alone never bleeds Condition C: case is unavailable. -/
theorem lds_cp_edge_alone_no_bleed (cpEdgeHeight binderHeight : Nat) :
    wlmForcesReconstruction
      (successiveCyclicChain [⟨.C, cpEdgeHeight, false⟩])
      binderHeight = true := by
  apply no_case_forces_reconstruction
  simp [successiveCyclicChain, List.map, PhaseEdgePosition.toChainPosition]

/-- LDS with a matrix case position above the binder bleeds Condition C.

    @cite{gong-2022} (41): embedded ACC object scrambled to matrix
    clause; matrix dative argument is the binder. Dependent ACC is
    available in the matrix clause (above the binder), so WLM bleeds. -/
theorem lds_matrix_case_bleeds (cpEdgeHeight matrixHeight binderHeight : Nat)
    (h : matrixHeight > binderHeight) :
    wlmBleedsCondC (ldsChainTemplate cpEdgeHeight matrixHeight true) binderHeight = true := by
  unfold ldsChainTemplate successiveCyclicChain
  simp only [List.map, PhaseEdgePosition.toChainPosition]
  exact wlm_bleeding_monotone _ _ _
    (case_above_binder_bleeds [] binderHeight matrixHeight h)

end Minimalism
