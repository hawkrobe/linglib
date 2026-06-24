import Linglib.Syntax.Minimalist.Labeling
import Linglib.Syntax.Minimalist.Features

/-!
# Phase Theory

Formalization of derivational phases following [chomsky-2000],
[abels-2012], and [citko-2014].

## Key Ideas

- CP and v*P are **phases**: derivational domains shipped to PF/LF incrementally
- **Phase Impenetrability Condition (PIC)**: material inside a phase complement
  becomes inaccessible once the phase is complete
- **Anti-locality**: complements of phase heads cannot move to
  Spec of the same phase head
- **Feature Inheritance**: C→T and v*→V inheritance

## Design

`isPhaseHeadOf c so` is derived from `outerCatC so` — the **projecting
(selection-driven) head**'s outer category ([marcolli-chomsky-berwick-2025]
Lemma 1.13.7). It is convention-independent (the selector projects regardless
of head side), so the former head-final trap no longer applies; the test is
also computable (no `Quot.out`), so concrete phase-head checks `decide`.
-/

namespace Minimalist

-- ============================================================================
-- Part 1: Phase Head Identification (derived from the selection-driven head)
-- ============================================================================

/-- Generic phase-head test: is the **projecting (selection-driven) head**
    of `so` exactly `c`? Uses `outerCatC` ([marcolli-chomsky-berwick-2025]
    Lemma 1.13.7 — the selector projects), so it is computable and
    convention-independent; `none` (≠ `some c`) at exocentric nodes. -/
def isPhaseHeadOf (c : Cat) (so : SyntacticObject) : Bool :=
  outerCatC so == some c

/-! ### Phase-head selectors

Only C is a phase head by default. [keine-2020] (ch. 5) argues that vP
is NOT a phase: φ-Agree and wh-licensing can cross unboundedly many vPs but
not CPs, selective opacity creates intractable problems for vP phases, and
previous arguments for vP phases (reconstruction, Dinka successive cyclicity,
Indonesian meN-deletion) can be reanalyzed.

For commonly-checked phase categories, call `isPhaseHeadOf` directly:

- C as phase head: `isPhaseHeadOf .C so` (linglib default per [keine-2020]).
  The classical Chomsky-2000/2001 extension to v as a phase head is
  `isPhaseHeadOf .C so || isPhaseHeadOf .v so`.

- D as phase head ([citko-2014] §2.5, [svenonius-2004]):
  `isPhaseHeadOf .D so`. Several analyses treat definite DPs as phases:
  extraction barriers ([chomsky-2000], [davies-dubinsky-2003],
  [shen-huang-2026] — definite island effect; VOCs neutralize via
  N/D-incorporation), scope barriers (QR cannot escape DP), spell-out
  domains (definite D triggers Transfer of its complement).

- SA as phase head: `isPhaseHeadOf .SA so`. SAP is the highest phase —
  since it cannot embed, allocutive agreement probing from SA is root-only.

**Voice/v* correspondence**: In the Kratzer/Schäfer framework,
agentive Voice = v*. But `Cat.Voice` can be either a phase head
(agentive) or not (anticausative). This flavor-level distinction
is tracked by `VoiceHead.IsPhasal` in
`Syntax/Minimalist/Voice.lean`, with the per-construction
override semantics described in that file's "Voice/Phase Bridge"
section. The two convergent recent clients of clause-internal Voice
phasehood are [erlewine-sommerlot-2025] (Malayic, A′-extraction)
and [pietraszko-2026] (Ndebele, A-movement & φ-agreement). -/

-- ============================================================================
-- Part 2: PIC Strength ([citko-2014] §2.4)
-- ============================================================================

/-- The strength of the Phase Impenetrability Condition.

    - `strong` (PIC₁, [chomsky-2000]): Only the edge (specifier) of the
      immediately lower phase is accessible. The complement is frozen
      as soon as the phase head is merged.
    - `weak` (PIC₂, [chomsky-2001]): The complement of a phase is accessible
      until the next higher phase head is merged.
    - `linearizationBound` (no PIC, [fox-pesetsky-2005], [sande-clem-dabkowski-2026]):
      No structural opacity at all — the only constraints on movement
      out of an already-spelled-out phase are the ordering statements
      emitted at that phase's spell-out (Cyclic Linearization). Material
      can be moved out of the complement of any phase, provided the
      resulting Ordering Table remains consistent. This is the regime
      argued for by SCD 2026 §6.2 (against both PIC₁ and PIC₂):
      Guébie discontinuous harmony requires that the particle, after
      being spelled out inside the lower vP phase, remains accessible
      to A′-fronting in the higher CP phase. Adopted independently by
      [branan-davis-2019], [lee-yip-2024] among others. See
      `Syntax/Minimalist/Linearization/Cyclic.lean` for the ordering-only
      locality machinery this mode delegates to.

      (Note: [halpert-2019]'s "Raising, unphased" is *also* a no-PIC
      account but a distinct mechanism — phasehood relativized to
      φ-probes (interaction/satisfaction + EPP), not Cyclic
      Linearization; see `Studies/Halpert2019.lean`.)

    Modular variants (e.g., the [d-alessandro-scheer-2015] "Modular PIC"
    proposal that PIC strength is parametrized per interface module) are
    not yet operationalized in this enum.

    TODO: the strong/weak distinction is not yet operationalized in
    `phaseImpenetrable`, which currently models only the structural
    "goal sits in the complement" check shared by both variants. The
    real distinction lies in *when* the check fires relative to merge
    of the next phase head — that requires a derivational timeline
    that this static API doesn't yet expose. Callers using `strong`
    or `weak` get the same structural answer; callers using
    `linearizationBound` should consult `Cyclic.SpelloutAndCheck`
    rather than `phaseImpenetrable`. -/
inductive PICStrength where
  | strong              -- PIC₁: complement frozen immediately
  | weak                -- PIC₂: complement accessible until next phase
  | linearizationBound  -- no opacity; only Cyclic Linearization constrains
  deriving Repr, DecidableEq

-- The mode-aware extraction predicate `admitsExtraction` is defined in
-- §4 below, after `phaseImpenetrable` (which it dispatches on for the
-- strict-PIC modes).

-- ============================================================================
-- Part 3: Phase Structure
-- ============================================================================

/-- A phase: a derivational cycle with head, complement, and edge.

    The phase head determines the domain boundary. Material in the
    complement is shipped to PF/LF; material at the edge remains
    accessible for further operations.

    Per-analysis discipline determines which heads count as phase heads
    — Keine 2020 (C-only), Chomsky 2000/2001 (C + v), Pietraszko 2026 +
    Erlewine & Sommerlot 2025 (also Voice via `VoiceHead.IsPhasal`),
    Citko 2014 (also D). The struct is intentionally permissive about
    `head`'s category so all four can register `Phase` instances. -/
structure Phase where
  /-- The phase head (per-analysis: C, v, Voice, D, …) -/
  head : SyntacticObject
  /-- The complement domain (shipped to interfaces) -/
  complement : SyntacticObject
  /-- The edge (specifier, accessible for further operations) -/
  edge : SyntacticObject

-- ============================================================================
-- Part 4: Phase Impenetrability Condition
-- ============================================================================

/-- The phase complement is the right daughter of the phase node under the
    **selection-induced** head-initial embedding (`selLinearize .initial`,
    [marcolli-chomsky-berwick-2025] Lemma 1.13.5): the phase head is the left
    daughter, its complement the right. Computable; supersedes the arbitrary
    `Quot.out` choice. `phaseComplementWith?` below takes an explicit head fn. -/
def phaseComplement? : SyntacticObject → Option SyntacticObject :=
  fun so => match selLinearize .initial so with
    | .of _ => none
    | .mul _ r => some (FreeCommMagma.mk r)

/-- Parameterized phase-complement accessor: under harmonic head-initial
    convention (head daughter to the LEFT of the planar representative),
    the complement is the RIGHT daughter of `h.section_.σ so`. Computable
    when `h.section_.σ` is.

    Returns `none` when `h.section_.σ so` is a leaf or trace (no daughter
    structure). For nodes, returns the right daughter as a `SyntacticObject`. -/
def phaseComplementWith? (h : HeadFunction) (so : SyntacticObject) :
    Option SyntacticObject :=
  match h.section_.σ so with
  | .of _ => none
  | .mul _ r => some (FreeCommMagma.mk r)

/-- Phase Impenetrability Condition: material inside a phase complement
    is inaccessible to operations outside the phase.

    The strong/weak (PIC₁/PIC₂) distinction is about *when* the check
    fires relative to the merge of the next phase head; structurally
    both variants ask the same question — is the goal sitting inside
    the phase's complement? — so this predicate is currently
    strength-agnostic. See `PICStrength` for the TODO. -/
def phaseImpenetrable (phase goal : SyntacticObject) : Prop :=
  match phaseComplement? phase with
  | some complement => contains complement goal
  | none => False

noncomputable instance (phase goal : SyntacticObject) :
    Decidable (phaseImpenetrable phase goal) := by
  unfold phaseImpenetrable
  cases phaseComplement? phase <;> classical infer_instance

/-- A phase admits movement of `goal` out of `phase.complement` under
    `strength`. For `strong`/`weak`, this is the negation of
    `phaseImpenetrable`. For `linearizationBound`, the predicate is
    vacuously `True` — actual constraint comes from the Cyclic
    Linearization table, not from phasehood per se.

    The point of the predicate is to make the SCD-2026 stance ("PIC
    is too strong, Cyclic Linearization is enough") expressible as a
    different `PICStrength` argument rather than a different theorem
    statement. Callers who pick `linearizationBound` should also
    feed the derivation through
    `Minimalist.Linearization.SpelloutAndCheck` to confirm it does
    not crash on ordering grounds. -/
def admitsExtraction (strength : PICStrength)
    (phase goal : SyntacticObject) : Prop :=
  match strength with
  | .strong | .weak => ¬ phaseImpenetrable phase goal
  | .linearizationBound => True

noncomputable instance (strength : PICStrength) (phase goal : SyntacticObject) :
    Decidable (admitsExtraction strength phase goal) := by
  unfold admitsExtraction
  cases strength <;> classical infer_instance

/-- Under `linearizationBound`, every phase admits extraction at the
    phasehood layer. Concrete crashes come from the linearization
    table (see `Minimalist.Linearization.SpelloutAndCheck`). This is the
    formal content of [sande-clem-dabkowski-2026]'s rejection of
    strict PIC. -/
theorem linearizationBound_admits_all (phase goal : SyntacticObject) :
    admitsExtraction .linearizationBound phase goal := trivial

/-- Strict PIC₁/PIC₂ both block extraction from a phase complement.
    The mode-as-data design lets a study file pick its locality regime
    by passing the `PICStrength` argument explicitly. -/
theorem strict_PIC_blocks {strength : PICStrength}
    (h : strength = .strong ∨ strength = .weak)
    {phase goal : SyntacticObject}
    (hp : phaseImpenetrable phase goal) :
    ¬ admitsExtraction strength phase goal := by
  rcases h with h | h <;> simp [admitsExtraction, h, hp]

-- ============================================================================
-- Part 5: Transfer
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
-- Part 6: Feature Inheritance / Transfer ([chomsky-2008], [ouali-2008],
--                                         [olivier-2026])
-- ============================================================================

/-! ### Feature Inheritance and KEEP/SHARE/DONATE

[chomsky-2008]'s feature inheritance has phase heads passing
operational features to their complements: C → T (tense/agreement),
v* → V (case/agreement). The phase head retains its edge features
while the inheritor takes over the agreement-driving features.

[ouali-2008] observes that "inheritance" is only one of three
possible feature operations on adjacent functional heads, and that the
choice is parametric (Berber agreement/anti-agreement is the empirical
diagnostic):

- **KEEP**: φ stays at the source head; the target lacks φ.
- **SHARE**: φ surfaces at both source and target. This explains
  clitic reduplication and is the operation [olivier-2026]
  argues for in Romance restructuring (Voice* → vMOD share).
- **DONATE**: φ moves source → target; the source loses φ. This is
  the classical [chomsky-2008] C → T / v* → V inheritance.

[olivier-2026] extends this typology to Voice* → vMOD feature
transfer in Romance restructuring clauses: under SHARE, φ-features
are present at vMOD as well as Voice*, which is what enables clitic
climbing (the climbing clitic enters Agree with the higher copy).
The KEEP / SHARE / DONATE choice is parametric across languages and
across constructions; we model it via a `style` field on
`FeatureInheritance`. -/

/-- Style of φ-feature transfer between two adjacent functional heads
    ([ouali-2008]).

    - `keep`: φ stays at source — target lacks φ.
    - `share`: φ surfaces at both source and target. Explains clitic
      reduplication and licenses clitic climbing in
      [olivier-2026]'s Voice* → vMOD analysis of Romance
      restructuring.
    - `donate`: φ moves source → target. The classical
      [chomsky-2008] C → T / v* → V inheritance. -/
inductive TransferStyle where
  | keep    -- φ stays at source
  | share   -- φ at source AND target
  | donate  -- φ moves source → target
  deriving DecidableEq, Repr

/-- Feature inheritance / sharing between two adjacent heads.

    Generalizes [chomsky-2008]'s C → T and v* → V inheritance
    (the `.donate` style) to cover [ouali-2008]'s
    KEEP/SHARE/DONATE typology and [olivier-2026]'s extension to
    Voice* → vMOD feature transfer in Romance restructuring clauses
    (the `.share` style). -/
structure FeatureInheritance where
  /-- The feature-bearing source head (phase head, Voice*, etc.). -/
  source : SyntacticObject
  /-- The head receiving features (T, V, vMOD). -/
  target : SyntacticObject
  /-- Source must immediately contain target. -/
  locality : immediatelyContains source target
  /-- Which transfer operation applies (default: classical
      [chomsky-2008] donate). -/
  style : TransferStyle := .donate
  /-- The features transferred (default: none specified at this layer). -/
  transferred : FeatureBundle := []

-- ============================================================================
-- Part 7: Phase-Bounded Locality
-- ============================================================================

/-- A movement is phase-bounded iff the mover does not cross a phase boundary.

    Under PIC, an element inside a phase complement is inaccessible.
    This means movement must target the edge before the phase is complete. -/
def isPhaseBounded (mover target : SyntacticObject)
    (phases : List Phase) : Prop :=
  ¬∃ ph ∈ phases, phaseImpenetrable ph.head mover ∧
    contains target ph.head

-- Phase-bounded locality subsumes Relativized Minimality ([rizzi-1990])
-- for Agree: if a goal is inside a phase complement, no probe outside can
-- reach it. The actual blocking-of-Agree statement lives downstream of the
-- Agree relation (see `Agree.validAgreeWithPIC`); a standalone theorem here
-- would just restate `phaseImpenetrable` as itself.

-- ============================================================================
-- Part 8: N/D-Incorporation and Phase Deactivation
-- ============================================================================

/-! ### N/D-Incorporation ([davies-dubinsky-2003], [shen-huang-2026])

[davies-dubinsky-2003] propose that verbs of creation (VOCs) trigger
LF noun incorporation: the head noun of the object DP incorporates into
the verb. This has the effect of neutralizing the DP's phasehood — the
D head is no longer a blocking category, and extraction from the DP
becomes possible.

[shen-huang-2026] adapt this analysis: it is the *determiner* that
undergoes covert head movement to the verb (following [boskovic-2015]
on phase collapse). The incorporation neutralizes the PIC, explaining why
VOCs ameliorate (but do not eliminate) definite island effects — the
Specificity Condition still applies independently.

Three conditions for incorporation ([davies-dubinsky-2003]:28–29):
1. The noun is a result nominal
2. The object is complement of a causative verb semantically related
   to the denoted result (e.g., *write-book*)
3. The verb's subject controls the agentive subject of the object -/

/-- Whether a DP's phase status has been deactivated by incorporation.

When `incorporated = true`, the D head has been absorbed into the
verb via head movement. The DP is no longer a phase boundary —
`isPhaseHeadOf .D` is irrelevant because the D head is no longer
projecting independently.

This models the effect described by [davies-dubinsky-2003] and
[shen-huang-2026]: VOCs neutralize the PIC for definite DPs.

The `wasPhase` field can be computed as `isPhaseHeadOf .D dHead` (now
computable via `outerCatC`), but is stored explicitly so a derivation can
record a phasehood decision that diverges from the bare categorial test. -/
structure DPPhaseStatus where
  /-- The D head (before incorporation) -/
  dHead : SyntacticObject
  /-- Whether D was originally a phase head. Set explicitly per
      derivation; in Phase 1.0 the substrate cannot compute this from
      `dHead` alone. -/
  wasPhase : Bool
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
  simp only [DPPhaseStatus.isActivePhase, h_phase, h_inc, Bool.not_true,
             Bool.and_false]

/-- Without incorporation, a D-phase remains active. -/
theorem no_incorporation_preserves (s : DPPhaseStatus)
    (h_phase : s.wasPhase = true) (h_no_inc : s.incorporated = false) :
    s.isActivePhase = true := by
  simp only [DPPhaseStatus.isActivePhase, h_phase, h_no_inc, Bool.not_false,
             Bool.and_true]

/-- Non-phases are never active barriers, regardless of incorporation. -/
theorem non_phase_never_active (s : DPPhaseStatus)
    (h : s.wasPhase = false) :
    s.isActivePhase = false := by
  simp only [DPPhaseStatus.isActivePhase, h, Bool.false_and]

end Minimalist
