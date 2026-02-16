import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# Voice and Applicative Derivations

Classic examples testing the Voice/Appl heads in Minimalist derivations.

## Derivations

1. **Transitive**: "John broke the vase"
   VoiceP [Voice_AG [vP [VP V DP]]]
   → Agentive Voice introduces the agent

2. **Anticausative**: "The vase broke"
   VoiceP [Voice_∅ [vP [VP V]]]
   → Non-thematic Voice: no agent, SE marks absent external arg

3. **Unaccusative**: "The ship sank"
   VoiceP [Voice_∅ [vP_GO [vP_BE [VP V]]]]
   → Inchoative structure, no external argument

4. **Ditransitive with low applicative**: "John sent Mary a letter"
   VoiceP [Voice_AG [vP [ApplP [Appl_low DP_goal [VP V DP_theme]]]]]

5. **High applicative (benefactive)**: "John baked Mary a cake"
   VoiceP [Voice_AG [ApplP [Appl_high DP_benef [vP [VP V DP_theme]]]]]

## References

- Kratzer, A. (1996). Severing the external argument from its verb.
- Pylkkänen, L. (2008). Introducing Arguments.
- Schäfer, F. (2008). The Syntax of (Anti-)Causatives.
-/

namespace Minimalism.Phenomena.VoiceAppl

-- ============================================================================
-- § 1: Derivation Building Blocks
-- ============================================================================

/-- A simplified derivation record for testing Voice/Appl structure.
    Tracks which heads are present and their properties.

    TODO: Replace with real `SyntacticObject` trees once the feature
    system on `SimpleLI` can encode sub-eventive heads (vDO/vGO/vBE).
    Currently these all map to `Cat.v`, losing the event-structural
    distinctions that drive inchoative/causative predictions. -/
structure VoiceApplDerivation where
  /-- Voice head (if present) -/
  voice : Option VoiceHead
  /-- Applicative type (if present) -/
  appl : Option ApplType
  /-- Event-structural heads (Cuervo 2003) -/
  verbHeads : List VerbHead
  /-- External argument present? -/
  hasExternalArg : Bool
  /-- Applied argument present? -/
  hasAppliedArg : Bool
  /-- Theme argument present? -/
  hasTheme : Bool
  deriving Repr, BEq

-- ============================================================================
-- § 2: Classic Derivations
-- ============================================================================

/-- "John broke the vase" — transitive with agentive Voice.
    [VoiceP John [Voice_AG [vP [VP broke [DP the vase]]]]] -/
def transitive_break : VoiceApplDerivation :=
  { voice := some voiceAgent
    appl := none
    verbHeads := [.vDO, .vGO, .vBE]
    hasExternalArg := true
    hasAppliedArg := false
    hasTheme := true }

/-- "The vase broke" — anticausative with non-thematic Voice.
    [VoiceP [Voice_∅ [vP_GO [vP_BE [VP broke]]]]]
    SE marks the non-thematic Voice at PF. -/
def anticausative_break : VoiceApplDerivation :=
  { voice := some voiceAnticausative
    appl := none
    verbHeads := [.vGO, .vBE]
    hasExternalArg := false
    hasAppliedArg := false
    hasTheme := false }

/-- "The ship sank" — unaccusative (inchoative, no agent).
    [VoiceP [Voice_∅ [vP_GO [vP_BE [VP sank]]]]] -/
def unaccusative_sink : VoiceApplDerivation :=
  { voice := some voiceAnticausative
    appl := none
    verbHeads := [.vGO, .vBE]
    hasExternalArg := false
    hasAppliedArg := false
    hasTheme := false }

/-- "John sent Mary a letter" — ditransitive with low applicative.
    [VoiceP John [Voice_AG [vP [ApplP Mary [Appl_low [VP sent [DP a letter]]]]]]] -/
def ditransitive_send : VoiceApplDerivation :=
  { voice := some voiceAgent
    appl := some .low
    verbHeads := [.vDO, .vGO, .vBE]
    hasExternalArg := true
    hasAppliedArg := true
    hasTheme := true }

/-- "John baked Mary a cake" — high applicative (benefactive).
    [VoiceP John [Voice_AG [ApplP Mary [Appl_high [vP [VP baked [DP a cake]]]]]]] -/
def benefactive_bake : VoiceApplDerivation :=
  { voice := some voiceAgent
    appl := some .high
    verbHeads := [.vDO]
    hasExternalArg := true
    hasAppliedArg := true
    hasTheme := true }

/-- "The door opened" — unaccusative change-of-state, middle voice.
    [vP_GO [vP_BE [VP opened]]]
    (No VoiceP at all — expletive/middle variant) -/
def middle_open : VoiceApplDerivation :=
  { voice := some voiceMiddle
    appl := none
    verbHeads := [.vGO, .vBE]
    hasExternalArg := false
    hasAppliedArg := false
    hasTheme := false }

-- ============================================================================
-- § 3: Structural Predictions
-- ============================================================================

/-- External argument iff agentive/causer Voice. -/
def predictsExternalArg (d : VoiceApplDerivation) : Bool :=
  match d.voice with
  | some v => v.assignsTheta
  | none => false

/-- Applied argument iff Appl head present. -/
def predictsAppliedArg (d : VoiceApplDerivation) : Bool :=
  d.appl.isSome

/-- Inchoative structure iff derivation has vGO ∧ vBE without vDO. -/
def isInchoativeDerivation (d : VoiceApplDerivation) : Bool :=
  isInchoative d.verbHeads

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- Transitive has an external argument (from agentive Voice). -/
theorem transitive_has_external :
    predictsExternalArg transitive_break = true := rfl

/-- Anticausative lacks an external argument (non-thematic Voice). -/
theorem anticausative_no_external :
    predictsExternalArg anticausative_break = false := rfl

/-- Unaccusative lacks an external argument. -/
theorem unaccusative_no_external :
    predictsExternalArg unaccusative_sink = false := rfl

/-- Ditransitive has both external and applied arguments. -/
theorem ditransitive_has_both :
    predictsExternalArg ditransitive_send = true ∧
    predictsAppliedArg ditransitive_send = true := ⟨rfl, rfl⟩

/-- High applicative benefactive has applied argument. -/
theorem benefactive_has_applied :
    predictsAppliedArg benefactive_bake = true := rfl

/-- Anticausative has inchoative structure. -/
theorem anticausative_is_inchoative :
    isInchoativeDerivation anticausative_break = true := by native_decide

/-- Transitive is NOT inchoative (has vDO). -/
theorem transitive_not_inchoative :
    isInchoativeDerivation transitive_break = false := by native_decide

/-- The causative alternation: transitive and anticausative share
    the inchoative core but differ in Voice flavor. -/
theorem causative_pair_shared_core :
    anticausative_break.verbHeads.all
      (transitive_break.verbHeads.contains ·) = true := by native_decide

/-- The causative pair differs in Voice: agentive vs non-thematic. -/
theorem causative_pair_voice_contrast :
    transitive_break.voice = some voiceAgent ∧
    anticausative_break.voice = some voiceAnticausative := ⟨rfl, rfl⟩

/-- Low applicative is below VP (recipient/goal). -/
theorem send_is_low_appl :
    ditransitive_send.appl = some .low := rfl

/-- High applicative is above VP (benefactive). -/
theorem bake_is_high_appl :
    benefactive_bake.appl = some .high := rfl

/-- Middle voice has no external argument and no semantics. -/
theorem middle_no_external :
    predictsExternalArg middle_open = false := rfl

-- ============================================================================
-- § 5: Voice/Phase Bridge
-- ============================================================================

/-- Agentive Voice corresponds to traditional v* (phase head).
    `isPhaseHead` in Phase.lean identifies phases via `Cat.v`, but in the
    Kratzer/Schäfer framework, agentive Voice replaces v*. The `phaseHead`
    field on `VoiceHead` tracks this distinction at the feature level. -/
theorem agentive_voice_is_phase_head :
    voiceAgent.phaseHead = true ∧ voiceCauser.phaseHead = true := ⟨rfl, rfl⟩

/-- Non-thematic and expletive Voice are NOT phase heads.
    Only θ-role-assigning Voice heads (agentive, causer) are phases. -/
theorem nonthematic_voice_not_phase_head :
    voiceAnticausative.phaseHead = false ∧ voiceMiddle.phaseHead = false := ⟨rfl, rfl⟩

/-- Phase-head-ness correlates with θ-role assignment:
    Voice is a phase head iff it assigns a θ-role. -/
theorem phase_iff_theta (v : VoiceHead)
    (h : v = voiceAgent ∨ v = voiceCauser ∨ v = voiceAnticausative ∨ v = voiceMiddle) :
    v.phaseHead = v.assignsTheta := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

end Minimalism.Phenomena.VoiceAppl
