import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Theories.Syntax.Minimalism.Core.VerbalDecomposition

/-!
# Voice Head Flavors (Kratzer 1996; Schäfer 2008)
@cite{chomsky-2001} @cite{coon-2019} @cite{cuervo-2003} @cite{harley-2014} @cite{kratzer-1996} @cite{legate-2003} @cite{schfer-2008}

Voice heads introduce (or fail to introduce) external arguments.
The key typology from Schäfer (2008):

- **Agentive**: Introduces an agent external argument (Kratzer 1996 Voice_AG)
- **Causer**: Introduces a causer (Schäfer 2008 Voice_CAUSE)
- **NonThematic**: Semantically vacuous — no θ-role, but has a [D] feature
  requiring PF realization (anticausative SE in Romance; Muñoz Pérez 2026)
- **Expletive**: No specifier, no semantics (middle voice, dispositionals)

## Key Claim (Muñoz Pérez 2026)

Non-thematic Voice contributes no semantics. SE is a PF marker of absent
external argument, not a semantic operator. Evidence: SE is optional in
Chilean Spanish when Fission produces a syncretic clitic.

## Voice–VerbHead Bridge (§§ 5–6)

Voice and VerbHead (Cuervo 2003) are both "little-v" but encode different
dimensions: Voice determines *whether* an external argument is introduced;
VerbHead decomposes the *event structure* into subevents. The bridge
formalizes Kratzer's (1996) insight in Cuervo's terms: agentive/causer Voice
contributes vDO (the agent's activity subevent) to the decomposition, while
non-thematic/expletive Voice contributes nothing. Combined with
root-determined lower structure (vGO, vBE), this yields the causative
alternation: Voice_AG + [vGO, vBE] = causative [vDO, vGO, vBE];
Voice_nonThematic + [vGO, vBE] = inchoative [vGO, vBE].

-/

namespace Minimalism

-- ============================================================================
-- § 1: Voice Flavors
-- ============================================================================

/-- Typology of Voice head flavors.

    Agentive Voice introduces an agent; causer Voice introduces a causer;
    non-thematic Voice has no semantics (anticausative SE);
    expletive Voice has neither specifier nor semantics (middles);
    passive Voice checks Case without assigning θ (Collins 2005: *by*). -/
inductive VoiceFlavor where
  | agentive     -- Introduces external argument with agent θ-role (Kratzer 1996)
  | causer       -- Introduces causer (Schäfer 2008: Voice_CAUSE)
  | nonThematic  -- Semantically vacuous, no θ-role (anticausative SE, Chuj -j)
  | expletive    -- No specifier, no semantics (middle voice)
  | impersonal   -- Demotes agent to implicit generic human (Finnish "passive")
  | passive      -- Checks Case but does not assign θ (Collins 2005: *by* heads VoiceP)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Voice Head Structure
-- ============================================================================

/-- A Voice head with its properties. -/
structure VoiceHead where
  /-- The flavor determining argument introduction and semantics -/
  flavor : VoiceFlavor
  /-- [D] subcategorization feature: requires a specifier at PF -/
  hasD : Bool
  /-- Is this Voice head a phase head? (v* = agentive Voice) -/
  phaseHead : Bool
  /-- Does this Voice head check Case? In active, v checks accusative;
      in passive, Voice/*by* checks it (Collins 2005, p. 96: feature
      dissociation). Default false — only passive Voice checks Case. -/
  checksCase : Bool := false
  /-- Agree-relevant features on Voice (e.g., [uOblique] for Mam =(y)a').
      Default empty — most Voice heads carry no probe features. -/
  features : FeatureBundle := []
  deriving DecidableEq, BEq, Repr

/-- Does this Voice head introduce a θ-role? -/
def VoiceHead.assignsTheta (v : VoiceHead) : Bool :=
  match v.flavor with
  | .agentive | .causer => true
  | .nonThematic | .expletive | .impersonal | .passive => false

/-- Does this Voice head have semantic content? -/
def VoiceHead.hasSemantics (v : VoiceHead) : Bool :=
  match v.flavor with
  | .agentive | .causer | .impersonal | .passive => true
  | .nonThematic | .expletive => false

-- ============================================================================
-- § 3: Canonical Voice Heads
-- ============================================================================

/-- Agentive Voice (transitive/unergative): introduces agent, is a phase head. -/
def voiceAgent : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := true }

/-- Causer Voice: introduces causer, is a phase head. -/
def voiceCauser : VoiceHead :=
  { flavor := .causer, hasD := true, phaseHead := true }

/-- Non-thematic Voice (anticausative): no θ-role, [D] for PF marking. -/
def voiceAnticausative : VoiceHead :=
  { flavor := .nonThematic, hasD := true, phaseHead := false }

/-- Expletive Voice (middle): no specifier, no semantics. -/
def voiceMiddle : VoiceHead :=
  { flavor := .expletive, hasD := false, phaseHead := false }

/-- Impersonal Voice (Finnish "passive"): demotes agent to an implicit
    generic human referent. Has semantics (existential closure over agent)
    but does not assign a θ-role to a syntactic specifier. -/
def voiceImpersonal : VoiceHead :=
  { flavor := .impersonal, hasD := false, phaseHead := false }

/-- Passive Voice (Collins 2005): headed by *by*, checks Case but does
    not assign a θ-role — v assigns the θ-role to the external argument
    in Spec,vP. Passive v is NOT a phase head: the Case-checking feature
    that makes v* a strong phase head has been dissociated onto Voice/*by*
    (Collins 2005, p. 96, p. 98).

    This is why PartP (complement of v) remains accessible for smuggling:
    passive v is a defective v, not v*. Cf. Chomsky (2001): "only v*
    (transitive) is a strong phase."

    **Contested**: Legate (2003) argues passive v IS a phase head based
    on reconstruction and parasitic gap data. The current formalization
    follows Collins (2005) and Chomsky (2001, 2008). -/
def voicePassive : VoiceHead :=
  { flavor := .passive, hasD := true, phaseHead := false, checksCase := true }

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- Agentive Voice assigns a θ-role. -/
theorem agentive_assigns_theta : voiceAgent.assignsTheta = true := rfl

/-- Non-thematic Voice does NOT assign a θ-role (Muñoz Pérez's key claim). -/
theorem nonThematic_no_theta : voiceAnticausative.assignsTheta = false := rfl

/-- Non-thematic Voice has no semantic contribution.
    This is the core claim of Muñoz Pérez (2026): SE is a PF phenomenon. -/
theorem nonThematic_no_semantics : voiceAnticausative.hasSemantics = false := rfl

/-- Agentive Voice is a phase head (v* = Voice_AG). -/
theorem agentive_is_phase : voiceAgent.phaseHead = true := rfl

/-- Non-thematic Voice is NOT a phase head. -/
theorem anticausative_not_phase : voiceAnticausative.phaseHead = false := rfl

/-- Impersonal Voice does NOT assign a θ-role (agent is existentially closed,
    not projected to a syntactic specifier). -/
theorem impersonal_no_theta : voiceImpersonal.assignsTheta = false := rfl

/-- Impersonal Voice HAS semantics: it contributes an existential closure
    over the agent variable, unlike non-thematic Voice which is vacuous. -/
theorem impersonal_has_semantics : voiceImpersonal.hasSemantics = true := rfl

/-- Passive Voice does NOT assign a θ-role (v does). -/
theorem passive_no_theta : voicePassive.assignsTheta = false := rfl

/-- Passive Voice IS NOT a phase head (Collins 2005, p. 98). -/
theorem passive_not_phase : voicePassive.phaseHead = false := rfl

/-- Passive Voice HAS semantic content (*by* mediates Case-checking). -/
theorem passive_has_semantics : voicePassive.hasSemantics = true := rfl

/-- Passive Voice checks Case (Collins 2005, p. 96: feature dissociation). -/
theorem passive_checks_case : voicePassive.checksCase = true := rfl

/-- Only agentive and causer Voice assign θ-roles. -/
theorem theta_implies_agentive_or_causer (v : VoiceHead) :
    v.assignsTheta = true → v.flavor = .agentive ∨ v.flavor = .causer := by
  cases v with | mk flavor _ _ =>
  cases flavor <;> simp [VoiceHead.assignsTheta]

-- ============================================================================
-- § 5: Voice–VerbHead Bridge (Kratzer 1996 in Cuervo 2003 terms)
-- ============================================================================

/-- The sub-eventive contribution of a Voice flavor.

    Agentive and causer Voice contribute vDO — the dynamic subevent
    where an external argument acts or causes. Non-thematic and expletive
    Voice contribute nothing: there is no agent subevent.

    This formalizes Kratzer's (1996) "severing" in Cuervo's (2003)
    event-decomposition vocabulary: the external argument's subevent
    comes from Voice, not from the root. -/
def VoiceFlavor.eventContribution : VoiceFlavor → Option VerbHead
  | .agentive    => some .vDO
  | .causer      => some .vDO
  | .nonThematic => none
  | .expletive   => none
  | .impersonal  => none
  | .passive     => none

/-- Build the full verbal decomposition by combining Voice's contribution
    with the root-determined lower event structure.

    The root supplies lower subevents (e.g., [vGO, vBE] for change-of-state
    roots). Voice optionally prepends vDO. The result is Cuervo's
    full decomposition:
    - Voice_AG + [vGO, vBE] → [vDO, vGO, vBE]  (causative)
    - Voice_nonTh + [vGO, vBE] → [vGO, vBE]     (inchoative)
    - Voice_AG + [] → [vDO]                      (unergative activity)
    - Voice_nonTh + [vBE] → [vBE]                (stative) -/
def buildDecomposition (voice : VoiceHead) (rootStructure : List VerbHead) :
    List VerbHead :=
  match voice.flavor.eventContribution with
  | some h => h :: rootStructure
  | none   => rootStructure

-- ============================================================================
-- § 6: Bridge Theorems
-- ============================================================================

/-- θ-assigning Voice contributes vDO. -/
theorem theta_voice_contributes_vDO (v : VoiceHead)
    (h : v.assignsTheta = true) :
    v.flavor.eventContribution = some .vDO := by
  cases v with | mk flavor _ _ _ =>
  cases flavor <;> simp [VoiceHead.assignsTheta] at h <;>
    simp [VoiceFlavor.eventContribution]

/-- Non-θ Voice contributes no subevent. -/
theorem no_theta_no_event (v : VoiceHead)
    (h : v.assignsTheta = false) :
    v.flavor.eventContribution = none := by
  cases v with | mk flavor _ _ _ =>
  cases flavor <;> simp [VoiceHead.assignsTheta, VoiceFlavor.eventContribution] at h ⊢

/-- Causative pattern: agentive Voice + [vGO, vBE] yields a causative decomposition. -/
theorem agent_plus_change_is_causative :
    isCausative (buildDecomposition voiceAgent [.vGO, .vBE]) = true := by
  native_decide

/-- Inchoative pattern: non-thematic Voice + [vGO, vBE] stays inchoative. -/
theorem nonthematic_plus_change_is_inchoative :
    isInchoative (buildDecomposition voiceAnticausative [.vGO, .vBE]) = true := by
  native_decide

/-- Activity pattern: agentive Voice + [] yields an activity. -/
theorem agent_plus_nothing_is_activity :
    isActivity (buildDecomposition voiceAgent []) = true := by
  native_decide

/-- State pattern: non-thematic Voice + [vBE] yields a state. -/
theorem nonthematic_plus_state_is_state :
    isState (buildDecomposition voiceAnticausative [.vBE]) = true := by
  native_decide

/-- The causative alternation: same root structure [vGO, vBE] is causative
    under agentive Voice but inchoative under non-thematic Voice. This is
    Coon's (2019) division of labor and Kratzer's (1996) severing in one
    theorem: alternation is determined by Voice, not by the root. -/
theorem causative_alternation :
    isCausative (buildDecomposition voiceAgent [.vGO, .vBE]) = true ∧
    isInchoative (buildDecomposition voiceAnticausative [.vGO, .vBE]) = true := by
  native_decide

/-- Voice determines causativity: if the root structure is [vGO, vBE],
    then whether the result is causative tracks exactly whether Voice
    assigns a θ-role. -/
theorem voice_determines_causativity_go_be (v : VoiceHead) :
    isCausative (buildDecomposition v [.vGO, .vBE]) = v.assignsTheta := by
  cases v with | mk flavor _ _ _ =>
  cases flavor <;> simp [buildDecomposition, VoiceFlavor.eventContribution,
    isCausative, VoiceHead.assignsTheta] <;> decide

-- ============================================================================
-- § 7: Feature Dissociation (Collins 2005, §4)
-- ============================================================================

/-- In active, v (= agentive Voice) assigns θ AND controls Case-checking
    (Case is checked by v, not by Voice). In passive, these functions
    dissociate: v assigns θ (external argument in Spec,vP), while Voice/*by*
    checks Case (Collins 2005, p. 96). -/
theorem active_theta_and_case_unified :
    voiceAgent.assignsTheta = true ∧ voiceAgent.checksCase = false := ⟨rfl, rfl⟩

/-- Passive: θ-assignment and Case-checking are dissociated.
    Voice does NOT assign θ (v does), but Voice DOES check Case. -/
theorem passive_theta_case_dissociated :
    voicePassive.assignsTheta = false ∧ voicePassive.checksCase = true := ⟨rfl, rfl⟩

/-- UTAH compliance (Collins 2005, p. 95): the external argument is
    structurally present (hasD = true) in BOTH active and passive.
    The external argument occupies the same position (Spec,vP)
    regardless of voice — satisfying the Uniformity of Theta Assignment
    Hypothesis. -/
theorem utah_active_passive :
    voiceAgent.hasD = true ∧ voicePassive.hasD = true := ⟨rfl, rfl⟩

/-- Passive Voice does not contribute vDO. In Collins' analysis, the
    activity subevent exists (the agent acts in both active and passive)
    but it is introduced by v, not by Voice. The current architecture
    tracks only Voice's contribution; v's contribution is implicit. -/
theorem passive_no_event_contribution :
    VoiceFlavor.passive.eventContribution = none := rfl

end Minimalism
