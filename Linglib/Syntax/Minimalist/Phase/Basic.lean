/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Phase.Domain
import Linglib.Syntax.Minimalist.Features

/-!
# Phase Theory (linguistic-facing API)

Formalization of derivational phases following [chomsky-2000], [abels-2012], and
[citko-2014], built **directly on the `SyntacticObject`-carrier phase domain**
(`Phase/Domain.lean`, MCB §1.14). This file packages the carrier-native
primitives (`SyntacticObject.isPhaseHeadOf`, `SyntacticObject.phase`/`phaseInterior`/`phaseEdge`,
`SyntacticObject.Impenetrable`, `SyntacticObject.isPhaseHead`) into the study-facing `Phase` record
+ the
PIC-strength / Transfer / feature-inheritance / DP-deactivation layer that the
paper-anchored study files consume.

## Key Ideas

- CP and v*P are **phases**: derivational domains shipped to PF/LF incrementally.
- **Phase Impenetrability Condition (PIC)**: material inside a phase complement
  becomes inaccessible once the phase is complete (= interior membership, MCB
  eq 1.14.3).
- **Feature Inheritance**: C→T and v*→V inheritance ([chomsky-2008]).

## Design

A `Phase` is a `tree`-relative `(tree, head)` pair: the head function on `SyntacticObject` is the
**selection-driven head** (`SyntacticObject.selHead`, Lemma 1.13.7), so the phase domain is read
off the carrier with no separate head-function field. Every phase notion delegates to
the `SyntacticObject.*` phase API, so concrete PIC checks `decide`. `isPhaseHeadOf c so` is the
projecting head's outer category — convention-independent (the carrier is unordered).
-/

namespace Minimalist

open SyntacticObject

-- ============================================================================
-- Part 1: Phase Head Identification (the selection-driven head)
-- ============================================================================

/-- Generic phase-head test: is the **projecting (selection-driven) head** of `so`
    exactly `c`? ([marcolli-chomsky-berwick-2025] Lemma 1.13.7 — the selector
    projects.) Computable and convention-independent; `none` (≠ `some c`) at
    exocentric nodes. -/
def isPhaseHeadOf (c : Cat) (so : SyntacticObject) : Bool := SyntacticObject.isPhaseHeadOf c so

/-! ### Phase-head selectors

Only C is a phase head by default. [keine-2020] (ch. 5) argues vP is NOT a phase. For
commonly-checked phase categories, call `isPhaseHeadOf` directly:

- C as phase head: `isPhaseHeadOf .C so` (linglib default per [keine-2020]). The
  classical [chomsky-2000]/2001 v extension is `isPhaseHeadOf .C so || isPhaseHeadOf .v so`.
- D as phase head ([citko-2014], [svenonius-2004]): `isPhaseHeadOf .D so` — definite
  DPs as extraction/scope/spell-out barriers ([davies-dubinsky-2003], [shen-huang-2026]).
- SA as phase head: `isPhaseHeadOf .SA so` — SAP is the highest phase, allocutive
  probing from SA is root-only.

**Voice/v* correspondence**: agentive Voice = v*, tracked by `Voice.Head.IsPhasal`
(`Voice.lean`); recent clause-internal-Voice-phase clients are
[erlewine-sommerlot-2025] (Malayic) and [pietraszko-2026] (Ndebele). -/

-- ============================================================================
-- Part 2: PIC Strength ([citko-2014])
-- ============================================================================

/-- The strength of the Phase Impenetrability Condition.

    - `strong` (PIC₁, [chomsky-2000]): only the edge of the immediately lower phase
      is accessible; the complement freezes when the phase head merges.
    - `weak` (PIC₂, [chomsky-2001]): the complement stays accessible until the next
      higher phase head merges.
    - `linearizationBound` (no PIC, [fox-pesetsky-2005], [sande-clem-dabkowski-2026]):
      no structural opacity — movement out of a spelled-out phase is constrained only
      by the Cyclic-Linearization ordering table ([branan-davis-2019], [lee-yip-2024]).
      SCD 2026 argue this regime for Guébie discontinuous harmony. (Distinct from
      [halpert-2019]'s φ-relativized "Raising, unphased".)

    The mode is **load-bearing**: it dispatches `admitsExtraction` and Agree's
    `validAgreeWithPIC`. Modular variants ([d-alessandro-scheer-2015]) are not yet
    operationalized. -/
inductive PICStrength where
  | strong              -- PIC₁: complement frozen immediately
  | weak                -- PIC₂: complement accessible until next phase
  | linearizationBound  -- no opacity; only Cyclic Linearization constrains
  deriving Repr, DecidableEq

-- ============================================================================
-- Part 3: Phase (MCB §1.14 — grounded in the selection head on `SyntacticObject`)
-- ============================================================================

/-- A **phase** ([marcolli-chomsky-berwick-2025] §1.14): a phase-head leaf `head`
    together with the containing tree `tree`. Phases are tree-relative; the head
    function is the carrier-native selection head (`SyntacticObject.selHead`), so no separate
    head-function field is needed. Every phase notion — content `Φ_ℓ` (eq 1.14.2),
    interior `Φ°_ℓ` (eq 1.14.3), edge `∂Φ_ℓ` (eq 1.14.4) — is a derived accessor over
    the `SyntacticObject.*` phase API.

    Per-analysis discipline (Keine 2020 C-only; Chomsky 2000/2001 C+v; Pietraszko 2026
    / Erlewine & Sommerlot 2025 also Voice; Citko 2014 also D) is expressed by *which
    leaf* a study supplies as `head`. -/
structure Phase where
  /-- The containing tree `T` (phases are `T`-relative, MCB §1.14). -/
  tree : SyntacticObject
  /-- The phase-head leaf `ℓ`; its maximal projection delimits the phase. -/
  head : LIToken

namespace Phase

/-- The whole phase `Φ_ℓ` — all accessible terms in the maximal projection
    (MCB eq 1.14.2). -/
def content (φ : Phase) : Multiset SyntacticObject := φ.tree.phase φ.head

/-- The interior `Φ°_ℓ` — the complement domain (= the head's c-command domain); the
    part the PIC freezes (MCB eq 1.14.3, "Z is the interior of the phase"). -/
def interior (φ : Phase) : Multiset SyntacticObject := φ.tree.phaseInterior φ.head

/-- The edge `∂Φ_ℓ` — head, specifiers, and modifiers; stays accessible
    (MCB eq 1.14.4). -/
def edge (φ : Phase) : Multiset SyntacticObject := φ.tree.phaseEdge φ.head

/-- **Phase Impenetrability Condition**: `goal` is frozen in this phase iff it lies in
    the interior. True by construction — the PIC *is* interior membership
    ([marcolli-chomsky-berwick-2025] §1.14). -/
def Impenetrable (φ : Phase) (goal : SyntacticObject) : Prop := goal ∈ φ.interior

instance (φ : Phase) (goal : SyntacticObject) : Decidable (φ.Impenetrable goal) :=
  inferInstanceAs (Decidable (goal ∈ φ.interior))

/-- A genuine phase: its head projects nontrivially (`head ∈ L_Φ(T)`, MCB Def 1.14.3
    eq 1.14.1) — `γ_ℓ` reaches an internal vertex. -/
def IsWellFormed (φ : Phase) : Prop := isPhaseHead φ.tree φ.head

instance (φ : Phase) : Decidable φ.IsWellFormed :=
  inferInstanceAs (Decidable (isPhaseHead _ _))

/-! ### Spell-out triggers

A payload dispatched at the spell-out of matching phases. The payload is generic: the
interpretive components read syntax, not conversely, so what a phase triggers — a
constraint subranking ([sande-jenks-inkelas-2020]'s cophonologies by phase,
`Phonology/OptimalityTheory/Cophonology.lean`), an allosemy rule, a realization rule —
lives with the consuming component, and this layer knows only the dispatch. -/

/-- A payload dispatched when a matching phase is spelled out: a phase-head predicate
bundled with the payload it activates over the phase complement. -/
structure Trigger (P : Type*) where
  /-- Predicate selecting which phase heads activate this trigger. -/
  selector : SyntacticObject → Bool
  /-- The payload dispatched over the matched phase. -/
  payload : P

variable {P : Type*}

/-- A trigger applies to a phase iff its `selector` matches the phase head (the head
leaf `ph.head`, as a leaf SyntacticObject). -/
def Trigger.appliesTo (tr : Trigger P) (ph : Phase) : Bool :=
  tr.selector (lexLeaf ph.head)

/-- The *first* registered trigger whose `selector` matches the phase head —
first-match encodes lexicographic precedence (the elsewhere ordering of
[sande-jenks-inkelas-2020]). `none` when no trigger matches. -/
def selectTrigger (registry : List (Trigger P)) (ph : Phase) : Option (Trigger P) :=
  registry.find? (·.appliesTo ph)

/-- The selected trigger, when present, applies to the phase. -/
theorem selectTrigger_applies {registry : List (Trigger P)} {ph : Phase} {tr : Trigger P}
    (h : selectTrigger registry ph = some tr) : tr.appliesTo ph = true := by
  unfold selectTrigger at h
  simpa using List.find?_some h

end Phase

-- ============================================================================
-- Part 4: Extraction under a PIC regime
-- ============================================================================

/-- Phase `φ` admits extraction of `goal` under `strength`:
    - `strong`/`weak`: `goal` is not frozen — `¬ φ.Impenetrable goal`.
    - `linearizationBound`: vacuously `True` — locality is enforced by Cyclic
      Linearization, not phasehood ([sande-clem-dabkowski-2026], [fox-pesetsky-2005]). -/
def admitsExtraction (strength : PICStrength) (φ : Phase)
    (goal : SyntacticObject) : Prop :=
  match strength with
  | .strong | .weak => ¬ φ.Impenetrable goal
  | .linearizationBound => True

instance (strength : PICStrength) (φ : Phase) (goal : SyntacticObject) :
    Decidable (admitsExtraction strength φ goal) := by
  unfold admitsExtraction; cases strength <;> infer_instance

/-- Under `linearizationBound`, every phase admits extraction at the phasehood layer;
    concrete crashes come from the linearization table. The formal content of
    [sande-clem-dabkowski-2026]'s rejection of strict PIC. -/
theorem linearizationBound_admits_all (φ : Phase) (goal : SyntacticObject) :
    admitsExtraction .linearizationBound φ goal := trivial

/-- Strict PIC₁/PIC₂ both block extraction of a goal frozen in the phase interior. -/
theorem strict_PIC_blocks {strength : PICStrength}
    (h : strength = .strong ∨ strength = .weak)
    {φ : Phase} {goal : SyntacticObject} (hp : φ.Impenetrable goal) :
    ¬ admitsExtraction strength φ goal := by
  rcases h with h | h <;> simp [admitsExtraction, h, hp]

-- ============================================================================
-- Part 5: Transfer
-- ============================================================================

/-- Transfer: ship a phase's interior `Φ°_ℓ` (= the complement domain, MCB eq 1.14.3)
    to the interfaces — PF (linearization, prosody) and LF (interpretation). -/
structure Transfer where
  /-- The phase being transferred. -/
  phase : Phase
  /-- Material sent to PF (phonological form). -/
  toPF : Multiset SyntacticObject
  /-- Material sent to LF (logical form). -/
  toLF : Multiset SyntacticObject
  /-- PF domain = interior. -/
  pf_is_interior : toPF = phase.interior
  /-- LF domain = interior. -/
  lf_is_interior : toLF = phase.interior

/-- Create a transfer from a phase (PF and LF receive the interior). -/
def Transfer.fromPhase (ph : Phase) : Transfer :=
  { phase := ph
    toPF := ph.interior
    toLF := ph.interior
    pf_is_interior := rfl
    lf_is_interior := rfl }

-- ============================================================================
-- Part 6: Feature Inheritance ([chomsky-2008], [ouali-2008], [olivier-2026])
-- ============================================================================

/-! ### Feature Inheritance and KEEP/SHARE/DONATE

[chomsky-2008]'s feature inheritance passes operational features from a phase head to
its complement (C → T, v* → V); the head keeps edge features. [ouali-2008] observes
"inheritance" is one of three parametric operations on adjacent functional heads
(Berber agreement/anti-agreement diagnoses the choice). [olivier-2026] extends the
typology to Voice* → vMOD transfer in Romance restructuring: under SHARE, φ surfaces at
vMOD as well, which is what licenses clitic climbing. -/

/-- Style of φ-feature transfer between two adjacent functional heads ([ouali-2008]).

    - `keep`: φ stays at source — target lacks φ.
    - `share`: φ surfaces at both source and target. Explains clitic reduplication and
      licenses clitic climbing in [olivier-2026]'s Voice* → vMOD analysis.
    - `donate`: φ moves source → target. The classical [chomsky-2008] C → T / v* → V
      inheritance. -/
inductive TransferStyle where
  | keep    -- φ stays at source
  | share   -- φ at source AND target
  | donate  -- φ moves source → target
  deriving DecidableEq, Repr

/-- Feature inheritance / sharing between two adjacent heads. Generalizes
    [chomsky-2008]'s C → T / v* → V inheritance (`.donate`) to [ouali-2008]'s
    KEEP/SHARE/DONATE typology and [olivier-2026]'s Voice* → vMOD `.share` extension. -/
structure FeatureInheritance where
  /-- The feature-bearing source head (phase head, Voice*, etc.). -/
  source : SyntacticObject
  /-- The head receiving features (T, V, vMOD). -/
  target : SyntacticObject
  /-- Source must immediately contain target. -/
  locality : immediatelyContains source target
  /-- Which transfer operation applies (default: classical [chomsky-2008] donate). -/
  style : TransferStyle := .donate
  /-- The features transferred (default: none specified at this layer). -/
  transferred : FeatureBundle := ⊥

-- ============================================================================
-- Part 7: Phase-Bounded Locality
-- ============================================================================

/-- A movement is phase-bounded iff the mover is not frozen in the interior of any of
    the given phases. Under PIC, an element inside a phase interior (= complement) is
    inaccessible; movement must reach the edge before the phase completes. -/
def isPhaseBounded (mover : SyntacticObject) (phases : List Phase) : Prop :=
  ¬ ∃ ph ∈ phases, ph.Impenetrable mover

-- ============================================================================
-- Part 8: N/D-Incorporation and Phase Deactivation
-- ============================================================================

/-! ### N/D-Incorporation ([davies-dubinsky-2003], [shen-huang-2026])

[davies-dubinsky-2003] propose verbs of creation (VOCs) trigger LF noun incorporation
— the object DP's head noun incorporates into the verb, neutralizing the DP's
phasehood so extraction becomes possible. [shen-huang-2026] adapt this: it is the
*determiner* that undergoes covert head movement (following [boskovic-2015] on phase
collapse), neutralizing the PIC and explaining why VOCs ameliorate (but do not
eliminate — the Specificity Condition still applies) definite island effects. -/

/-- Whether a DP's phase status has been deactivated by incorporation.

    When `incorporated = true`, the D head has been absorbed into the verb via head
    movement, so the DP is no longer a phase boundary. Models the [davies-dubinsky-2003]
    / [shen-huang-2026] VOC neutralization of the PIC for definite DPs. `wasPhase` is
    stored explicitly so a derivation can record a phasehood decision diverging from the
    bare categorial test `isPhaseHeadOf .D dHead`. -/
structure DPPhaseStatus where
  /-- The D head (before incorporation). -/
  dHead : SyntacticObject
  /-- Whether D was originally a phase head (set explicitly per derivation). -/
  wasPhase : Bool
  /-- Whether incorporation has applied. -/
  incorporated : Bool

/-- A DP is an active phase barrier iff it was originally a phase AND has not been
    deactivated by incorporation. -/
def DPPhaseStatus.isActivePhase (s : DPPhaseStatus) : Bool :=
  s.wasPhase && !s.incorporated

/-- Incorporation deactivates phasehood: a D-phase that undergoes incorporation is no
    longer an active phase barrier. -/
theorem incorporation_deactivates (s : DPPhaseStatus)
    (h_phase : s.wasPhase = true) (h_inc : s.incorporated = true) :
    s.isActivePhase = false := by
  simp only [DPPhaseStatus.isActivePhase, h_phase, h_inc, Bool.not_true, Bool.and_false]

/-- Without incorporation, a D-phase remains active. -/
theorem no_incorporation_preserves (s : DPPhaseStatus)
    (h_phase : s.wasPhase = true) (h_no_inc : s.incorporated = false) :
    s.isActivePhase = true := by
  simp only [DPPhaseStatus.isActivePhase, h_phase, h_no_inc, Bool.not_false, Bool.and_true]

/-- Non-phases are never active barriers, regardless of incorporation. -/
theorem non_phase_never_active (s : DPPhaseStatus) (h : s.wasPhase = false) :
    s.isActivePhase = false := by
  simp only [DPPhaseStatus.isActivePhase, h, Bool.false_and]

end Minimalist
