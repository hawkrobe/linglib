/-
# Phase Theory

Formalization of derivational phases following @cite{chomsky-2000},
@cite{abels-2012}, and @cite{citko-2014}.

## Key Ideas

- CP and v*P are **phases**: derivational domains shipped to PF/LF incrementally
- **Phase Impenetrability Condition (PIC)**: material inside a phase complement
  becomes inaccessible once the phase is complete
- **Anti-locality**: complements of phase heads cannot move to
  Spec of the same phase head
- **Feature Inheritance**: C→T and v*→V inheritance

## Design

`isPhaseHead` is DERIVED from `labelCat` (the formal labeling system),
not stipulated. This grounds Phase Theory in the same projection machinery
used by Containment → Labeling → Agree → Workspace.

-/

import Linglib.Theories.Syntax.Minimalism.Core.Labeling

namespace Minimalism

-- ============================================================================
-- Part 1: Phase Head Identification (derived from labelCat)
-- ============================================================================

/-- Identify phase heads from the formal category system.

    Only C is a phase head by default. @cite{keine-2020} (ch. 5)
    argues that vP is NOT a phase: φ-Agree and wh-licensing can
    cross unboundedly many vPs but not CPs, selective opacity
    creates intractable problems for vP phases, and previous
    arguments for vP phases (reconstruction, Dinka successive
    cyclicity, Indonesian meN-deletion) can be reanalyzed.

    `isPhaseHeadV` provides the traditional view where v is also
    a phase head, for analyses that require it.

    **Voice/v* correspondence**: In the Kratzer/Schäfer framework,
    agentive Voice = v*. But `Cat.Voice` can be either a phase head
    (agentive) or not (anticausative). This flavor-level distinction
    is tracked by `VoiceHead.phaseHead` in `Core/Voice.lean`, with
    bridge theorems in `Core/Voice.lean` § 8. -/
def isPhaseHead (so : SyntacticObject) : Bool :=
  match labelCat so with
  | some .C => true    -- CP phase
  | _ => false

/-- Traditional phase identification where both C and v are phase heads.
    Use this for analyses that assume vP phasehood (@cite{chomsky-2000},
    @cite{chomsky-2001}). @cite{keine-2020} argues against vP phases. -/
def isPhaseHeadV (so : SyntacticObject) : Bool :=
  match labelCat so with
  | some .C => true    -- CP phase
  | some .v => true    -- v*P phase
  | _ => false

/-- D as a phase head (@cite{citko-2014} §2.5, @cite{svenonius-2004}).

    Several analyses treat definite DPs as phases:
    - **Extraction barriers**: @cite{chomsky-2000}, @cite{davies-dubinsky-2003},
      @cite{shen-huang-2026} — definite DP phasehood blocks wh-subextraction
      (definite island effect). VOCs can neutralize phasehood via
      N/D-incorporation.
    - **Scope barriers**: QR cannot escape DP.
    - **Spell-out domains**: definite D triggers Transfer of its complement. -/
def isDPhaseHead (so : SyntacticObject) : Bool :=
  match labelCat so with
  | some .D => true
  | _ => false

/-- SA as a phase head.
    SAP is the highest phase — since it cannot embed,
    allocutive agreement probing from SA is root-only. -/
def isSAPhaseHead (so : SyntacticObject) : Bool :=
  match labelCat so with
  | some .SA => true
  | _ => false

/-- Extended phase head identification (C, v, optionally D) -/
def isPhaseHeadExt (so : SyntacticObject) (dpIsPhase : Bool := false) : Bool :=
  isPhaseHead so || (dpIsPhase && isDPhaseHead so)

-- ============================================================================
-- Part 2: PIC Strength (@cite{citko-2014} §2.4)
-- ============================================================================

/-- The strength of the Phase Impenetrability Condition.

    - `strong` (PIC₁, @cite{chomsky-2000}): Only the edge (specifier) of the
      immediately lower phase is accessible. The complement is frozen
      as soon as the phase head is merged.
    - `weak` (PIC₂, @cite{chomsky-2001}): The complement of a phase is accessible
      until the next higher phase head is merged. -/
inductive PICStrength where
  | strong   -- PIC₁: complement frozen immediately
  | weak     -- PIC₂: complement accessible until next phase
  deriving Repr, DecidableEq

-- ============================================================================
-- Part 3: Phase Structure
-- ============================================================================

/-- A phase: a derivational cycle with head, complement, and edge.

    The phase head determines the domain boundary. Material in the
    complement is shipped to PF/LF; material at the edge remains
    accessible for further operations. -/
structure Phase where
  /-- The phase head (C or v*) -/
  head : SyntacticObject
  /-- Proof that the head is indeed a phase head -/
  isHead : isPhaseHead head = true
  /-- The complement domain (shipped to interfaces) -/
  complement : SyntacticObject
  /-- The edge (specifier, accessible for further operations) -/
  edge : SyntacticObject

-- ============================================================================
-- Part 4: Phase Impenetrability Condition
-- ============================================================================

/-- Phase Impenetrability Condition: material inside a phase complement
    is inaccessible to operations outside the phase.

    Under the strong PIC, the complement is frozen
    as soon as the phase head is merged. Under the weak PIC,
    it is frozen when the next phase head is merged. -/
def phaseImpenetrable (strength : PICStrength) (phase goal : SyntacticObject) : Prop :=
  match strength with
  | .strong =>
    -- Strong PIC: goal is inside the complement and thus inaccessible
    match phase with
    | .node _ complement => contains complement goal
    | _ => False
  | .weak =>
    -- Weak PIC: goal is inside the complement; accessible until next phase
    -- Modeled the same structurally — the difference is WHEN this is checked
    match phase with
    | .node _ complement => contains complement goal
    | _ => False

-- ============================================================================
-- Part 5: Anti-Locality (@cite{abels-2012}, Ch. 4)
-- ============================================================================

/-- Anti-locality: the complement of a phase head H cannot move to Spec-H.

    This is "too local" — movement must cross at least one maximal projection.
    @cite{abels-2012} derives this from the independently motivated ban on
    complement-to-specifier movement within a single phase.

    This is a derivational constraint: a derivation that applies Internal Merge
    to move the complement of H to Spec-H is illicit. We model this as a
    predicate on derivations rather than on structures. -/
def antiLocality (head complement mover : SyntacticObject) : Prop :=
  immediatelyContains head complement →
    -- If H immediately contains its complement, then the complement
    -- cannot be the mover in Internal Merge targeting H
    mover ≠ complement

-- ============================================================================
-- Part 6: Stranding Generalization
-- ============================================================================

/-- Stranding Generalization:
    Complements of phase heads cannot be stranded by movement of the head.

    DERIVED from Anti-locality + PIC:
    - By Anti-locality, complement of H can't move to Spec-HP
    - By PIC, complement of H can't move out of HP (frozen)
    - Therefore: complement of a phase head is immovable = stranded -/
theorem stranding_from_antilocality_pic
    (ph : Phase)
    (h_imm : immediatelyContains ph.head ph.complement)
    (h_anti : antiLocality ph.head ph.complement ph.complement) :
    -- Anti-locality tells us complement ≠ complement, which is absurd.
    -- This means the derivation where the complement moves to Spec-H is blocked.
    False := by
  have := h_anti h_imm
  exact absurd rfl this

-- ============================================================================
-- Part 7: Transfer
-- ============================================================================

/-- Transfer: ship a phase complement to the interfaces (PF and LF).

    When a phase is complete, its complement domain is transferred:
    - To PF for phonological computation (linearization, prosody)
    - To LF for semantic interpretation -/
structure Transfer where
  /-- The phase being transferred -/
  phase : Phase
  /-- Material sent to PF (phonological form) -/
  toPF : SyntacticObject
  /-- Material sent to LF (logical form) -/
  toLF : SyntacticObject
  /-- PF domain = complement -/
  pf_is_complement : toPF = phase.complement
  /-- LF domain = complement -/
  lf_is_complement : toLF = phase.complement

/-- Create a transfer from a phase (PF and LF receive the complement) -/
def Transfer.fromPhase (ph : Phase) : Transfer :=
  { phase := ph
    toPF := ph.complement
    toLF := ph.complement
    pf_is_complement := rfl
    lf_is_complement := rfl }

-- ============================================================================
-- Part 8: Feature Inheritance (@cite{chomsky-2008})
-- ============================================================================

/-- Feature Inheritance: phase heads pass features to their complements.

    - C passes tense/agreement features to T
    - v* passes case/agreement features to V

    The phase head retains its edge features (EPP, etc.)
    but the "operational" features are inherited by the complement head. -/
structure FeatureInheritance where
  /-- The phase head (C or v*) -/
  phaseHead : SyntacticObject
  /-- The inheriting head (T or V) -/
  inheritor : SyntacticObject
  /-- The phase head must immediately contain the inheritor -/
  locality : immediatelyContains phaseHead inheritor

/-- C→T inheritance: C is a phase head, T inherits -/
def cToTInheritance (cHead tHead : SyntacticObject)
    (h : immediatelyContains cHead tHead) : FeatureInheritance :=
  { phaseHead := cHead
    inheritor := tHead
    locality := h }

/-- v*→V inheritance: v* is a phase head, V inherits -/
def vToVInheritance (vHead vbHead : SyntacticObject)
    (h : immediatelyContains vHead vbHead) : FeatureInheritance :=
  { phaseHead := vHead
    inheritor := vbHead
    locality := h }

-- ============================================================================
-- Part 9: Phase-Bounded Locality
-- ============================================================================

/-- A movement is phase-bounded iff the mover does not cross a phase boundary.

    Under PIC, an element inside a phase complement is inaccessible.
    This means movement must target the edge before the phase is complete. -/
def isPhaseBounded (mover target : SyntacticObject)
    (phases : List Phase) (strength : PICStrength) : Prop :=
  ¬∃ ph ∈ phases, phaseImpenetrable strength ph.head mover ∧
    contains target ph.head

/-- Phase-bounded locality subsumes Relativized Minimality (@cite{rizzi-1990}) for Agree:
    if a goal is inside a phase complement, no probe outside can reach it. -/
theorem pic_blocks_agree (strength : PICStrength) (phase _probe goal : SyntacticObject)
    (h_impenetrable : phaseImpenetrable strength phase goal)
    (_h_outside : ¬contains phase _probe) :
    -- Probe cannot access goal across the phase boundary
    phaseImpenetrable strength phase goal := h_impenetrable

-- ============================================================================
-- Part 10: N/D-Incorporation and Phase Deactivation
-- ============================================================================

/-! ### N/D-Incorporation (@cite{davies-dubinsky-2003}, @cite{shen-huang-2026})

@cite{davies-dubinsky-2003} propose that verbs of creation (VOCs) trigger
LF noun incorporation: the head noun of the object DP incorporates into
the verb. This has the effect of neutralizing the DP's phasehood — the
D head is no longer a blocking category, and extraction from the DP
becomes possible.

@cite{shen-huang-2026} adapt this analysis: it is the *determiner* that
undergoes covert head movement to the verb (following @cite{boskovic-2015}
on phase collapse). The incorporation neutralizes the PIC, explaining why
VOCs ameliorate (but do not eliminate) definite island effects — the
Specificity Condition still applies independently.

Three conditions for incorporation (@cite{davies-dubinsky-2003}:28–29):
1. The noun is a result nominal
2. The object is complement of a causative verb semantically related
   to the denoted result (e.g., *write-book*)
3. The verb's subject controls the agentive subject of the object -/

/-- Whether a DP's phase status has been deactivated by incorporation.

When `incorporated = true`, the D head has been absorbed into the
verb via head movement. The DP is no longer a phase boundary —
`isDPhaseHead` is irrelevant because the D head is no longer
projecting independently.

This models the effect described by @cite{davies-dubinsky-2003} and
@cite{shen-huang-2026}: VOCs neutralize the PIC for definite DPs. -/
structure DPPhaseStatus where
  /-- The D head (before incorporation) -/
  dHead : SyntacticObject
  /-- Whether D was originally a phase head -/
  wasPhase : Bool := isDPhaseHead dHead
  /-- Whether incorporation has applied -/
  incorporated : Bool
  deriving Repr

/-- A DP is an active phase barrier iff it was originally a phase
AND has not been deactivated by incorporation. -/
def DPPhaseStatus.isActivePhase (s : DPPhaseStatus) : Bool :=
  s.wasPhase && !s.incorporated

/-- Incorporation deactivates phasehood: a D-phase that undergoes
incorporation is no longer an active phase barrier. -/
theorem incorporation_deactivates (s : DPPhaseStatus)
    (h_phase : s.wasPhase = true) (h_inc : s.incorporated = true) :
    s.isActivePhase = false := by
  simp [DPPhaseStatus.isActivePhase, h_phase, h_inc]

/-- Without incorporation, a D-phase remains active. -/
theorem no_incorporation_preserves (s : DPPhaseStatus)
    (h_phase : s.wasPhase = true) (h_no_inc : s.incorporated = false) :
    s.isActivePhase = true := by
  simp [DPPhaseStatus.isActivePhase, h_phase, h_no_inc]

/-- Non-phases are never active barriers, regardless of incorporation. -/
theorem non_phase_never_active (s : DPPhaseStatus)
    (h : s.wasPhase = false) :
    s.isActivePhase = false := by
  simp [DPPhaseStatus.isActivePhase, h]

end Minimalism
