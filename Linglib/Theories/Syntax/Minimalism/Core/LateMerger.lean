import Linglib.Theories.Syntax.Minimalism.Core.DependentCase

/-!
# Wholesale Late Merger
@cite{takahashi-hulsey-2009} @cite{lebeaux-1988}

Wholesale late merger (WLM) allows the NP restrictor of a moved DP
to merge countercyclically at a position on the movement chain where
case can be assigned, rather than at the base position. This is an
updated and expanded version of @cite{lebeaux-1988}'s late merger
operation for adjuncts.

## Core idea

Under the copy theory of movement, a moved DP leaves copies at every
position on its chain. WLM allows the NP restrictor to be introduced
at *any* copy position, so long as the resulting DP can receive case.

## Condition C interaction

If the NP restrictor contains an R-expression that would be
c-commanded by a coreferential pronoun at the base position, full
reconstruction triggers a Condition C violation. WLM can avoid this
by introducing the restrictor at a higher copy position — but only if
case is available there.

@cite{gong-2022} shows that this case requirement is the key factor
controlling Condition C reconstruction effects in Mongolian scrambling:
reconstruction tracks case positions, not the A/A-bar distinction.

## Definitions

- `ChainPosition` — a position on a movement chain with its height and
  case availability
- `wlmBleedsCondC` — whether WLM can avoid Condition C by merging
  the restrictor above the binder
- `wlmForcesReconstruction` — the restrictor must merge below the
  binder (no case position above)
-/

namespace Minimalism

-- ============================================================================
-- S 1: Chain Positions
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
-- S 2: WLM and Condition C
-- ============================================================================

/-- Wholesale late merger bleeds Condition C iff there exists a position
    on the movement chain that is (a) strictly above the pronoun binder
    and (b) a position where case can be assigned.

    When such a position exists, the NP restrictor can merge there,
    placing the R-expression outside the c-command domain of the
    binder and avoiding a Condition C violation.

    @cite{gong-2022} condition (2): WLM may bleed Condition C if the
    movement chain permits a case position higher than the pronoun
    binder. -/
def wlmBleedsCondC (chain : List ChainPosition) (binderHeight : Nat) : Bool :=
  chain.any (λ cp => cp.caseAvailable && cp.height > binderHeight)

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
-- S 3: Structural Properties
-- ============================================================================

/-- If every chain position is at or below the binder, WLM forces
    reconstruction. -/
theorem top_binder_forces_reconstruction
    (chain : List ChainPosition) (binderHeight : Nat)
    (h : ∀ cp ∈ chain, cp.height ≤ binderHeight) :
    wlmForcesReconstruction chain binderHeight = true := by
  unfold wlmForcesReconstruction wlmBleedsCondC
  simp only [Bool.not_eq_true']
  rw [List.any_eq_false]
  intro cp hmem
  have hle := h cp hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨_, hgt⟩
  omega

/-- A case position above the binder guarantees WLM bleeds Condition C. -/
theorem case_above_binder_bleeds
    (chain : List ChainPosition) (binderHeight h : Nat)
    (hgt : h > binderHeight) :
    wlmBleedsCondC (⟨h, true⟩ :: chain) binderHeight = true := by
  simp only [wlmBleedsCondC, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
             decide_eq_true_eq, true_and]
  left; exact hgt

/-- WLM bleeding is monotone: adding positions never removes it. -/
theorem wlm_bleeding_monotone
    (chain : List ChainPosition) (cp : ChainPosition) (binderHeight : Nat)
    (h : wlmBleedsCondC chain binderHeight = true) :
    wlmBleedsCondC (cp :: chain) binderHeight = true := by
  simp only [wlmBleedsCondC, List.any_cons, Bool.or_eq_true]
  right; exact h

/-- If no chain position has case available, WLM forces reconstruction
    regardless of heights. -/
theorem no_case_forces_reconstruction
    (chain : List ChainPosition) (binderHeight : Nat)
    (h : ∀ cp ∈ chain, cp.caseAvailable = false) :
    wlmForcesReconstruction chain binderHeight = true := by
  unfold wlmForcesReconstruction wlmBleedsCondC
  simp only [Bool.not_eq_true']
  rw [List.any_eq_false]
  intro cp hmem
  simp [h cp hmem]

-- ============================================================================
-- S 4: Condition C over Syntactic Objects
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
-- S 5: Successive-Cyclic Movement and Phase Edges
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
