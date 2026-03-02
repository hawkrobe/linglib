import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Semantics.Events.ThematicRoles
import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking

/-!
# Severing Account of θ-Role Assignment

@cite{kratzer-1996} @cite{schaefer-2008} @cite{alexiadou-schfer-2015} @cite{levin-2004} @cite{schfer-2008}The **severing** account holds that the Voice head — @cite{goldberg-1995}
not the verb root — determines which theta role the external argument
gets. The verb root is category-neutral; argument structure comes from
the functional sequence.

Note: this is sometimes called the "constructionist" position, but that
term is better reserved for Construction Grammar, which makes a different (stronger) claim. The Minimalist Voice
analysis is specifically Kratzer's **severing** of the external argument.

## The prediction

`VoiceFlavor.thetaRole` maps each Voice flavor to the theta role
it assigns. The current typology has
exactly two θ-assigning flavors:

- Voice_AG → agent
- Voice_CAUSE → stimulus

This makes a clear empirical prediction: all external arguments
introduced by Voice must be either agents or stimuli. Experiencer
subjects (know, believe, enjoy) require either:
- additional Voice flavors not in the current typology, or
- some other mechanism outside Voice

## Voice compatibility

`compatibleVoices` derives which Voice flavors a verb is compatible
with, based on independently motivated VerbCore properties. This
captures @cite{levin-2004}'s gradient verb–construction pairing: causative
alternation verbs (break, melt, open) are compatible with BOTH
Voice_AG and Voice_nonThematic, while non-alternating verbs have a
single compatible Voice.

## As a LinkingTheory

`severingAccount` packages the severing prediction as a `LinkingTheory
VoiceFlavor`, allowing uniform comparison with other accounts via the
shared linking interface.

-/

namespace Theories.Interfaces.SyntaxSemantics.VoiceTheta

open _root_.Minimalism (VoiceFlavor VoiceHead voiceAgent voiceCauser
  voiceAnticausative voiceMiddle voiceImpersonal)
open Core.Verbs (VerbCore ControlType SenseTag)
open Semantics.Causation.PsychCausation (CausalSource)
open _root_.Interfaces.SyntaxSemantics (LinkingTheory ArgPosition)

-- ════════════════════════════════════════════════════════════════════
-- § 1. Voice flavor → theta role (the severing prediction)
-- ════════════════════════════════════════════════════════════════════

/-- Severing prediction:
    Voice flavor determines WHICH theta role the external argument gets.

    This goes beyond `assignsTheta` (which only says WHETHER there is one)
    to predict the specific role. The current typology has only two
    θ-assigning flavors, so it can only distinguish agent from stimulus. -/
def _root_.Minimalism.VoiceFlavor.thetaRole : VoiceFlavor → Option ThetaRole
  | .agentive    => some .agent
  | .causer      => some .stimulus
  | .nonThematic => none
  | .expletive   => none
  | .impersonal  => none
  | .passive     => none

/-- Voice_AG predicts agent. -/
theorem agentive_predicts_agent :
    VoiceFlavor.thetaRole .agentive = some .agent := rfl

/-- Voice_CAUSE predicts stimulus. -/
theorem causer_predicts_stimulus :
    VoiceFlavor.thetaRole .causer = some .stimulus := rfl

/-- Non-θ Voice predicts no theta role. -/
theorem nonthematic_predicts_none :
    VoiceFlavor.thetaRole .nonThematic = none := rfl

-- ════════════════════════════════════════════════════════════════════
-- § 2. Verb → Voice selection (canonical Voice for each verb)
-- ════════════════════════════════════════════════════════════════════

/-- Derive the canonical Voice flavor a verb projects from VerbCore
    properties. This is the "default" or most typical configuration.

    - `causalSource.isSome` → Voice_CAUSE (Class II psych, Kim 2024)
    - `unaccusative` → Voice_nonThematic (anticausative)
    - `controlType =.raising` → Voice_expletive (no external argument)
    - `levinClass =.weather` → Voice_expletive (expletive subject)
    - default → Voice_AG (agentive) -/
def selectedVoice (v : VerbCore) : VoiceFlavor :=
  if v.causalSource.isSome then .causer
  else if v.unaccusative then .nonThematic
  else if v.controlType == .raising then .expletive
  else if v.levinClass == some .weather then .expletive
  else .agentive

-- ════════════════════════════════════════════════════════════════════
-- § 3. Gradient Voice compatibility (Levin 2004)
-- ════════════════════════════════════════════════════════════════════

/-- Which Voice flavors is this verb compatible with?

    Most verbs have a single compatible Voice (categorical). Causative
    alternation verbs are compatible with both Voice_AG (transitive)
    and Voice_nonThematic (inchoative) — this is the gradient
    verb–construction pairing that @cite{levin-2004} identifies.

    The current implementation uses `selectedVoice` as the sole element.
    TODO: extend to detect alternating verbs via MeaningComponents
    (changeOfState ∧ causation ∧ ¬instrumentSpec → [.agentive,.nonThematic]). -/
def compatibleVoices (v : VerbCore) : List VoiceFlavor :=
  [selectedVoice v]

-- ════════════════════════════════════════════════════════════════════
-- § 4. The severing prediction chain
-- ════════════════════════════════════════════════════════════════════

/-- The severing prediction for external argument theta role:
    verb → Voice selection → theta role.

    Verb semantics determines which Voice head is projected (§ 2),
    and Voice flavor determines the theta role (§ 1). -/
def severingTheta (v : VerbCore) : Option ThetaRole :=
  (selectedVoice v).thetaRole

-- ════════════════════════════════════════════════════════════════════
-- § 5. LinkingTheory instance
-- ════════════════════════════════════════════════════════════════════

/-- The severing account as a `LinkingTheory`.

    Structural context = `VoiceFlavor`. The `predict` function ignores
    the verb — Voice alone determines the external argument's theta
    role. The verb's contribution is channeled entirely through
    `compatible` (which determines which Voice flavors are available). -/
def severingAccount : LinkingTheory VerbCore VoiceFlavor where
  compatible := compatibleVoices
  predict := fun _verb vf pos =>
    match pos with
    | .subject => vf.thetaRole
    | _ => none  -- Voice only predicts the external argument

-- ════════════════════════════════════════════════════════════════════
-- § 6. Lexicalist account as LinkingTheory (for comparison)
-- ════════════════════════════════════════════════════════════════════

/-- The lexicalist account (Levin 1993, Rappaport Hovav & Levin 1998)
    as a `LinkingTheory`.

    Structural context = `Unit` — the verb's lexical semantics
    determines theta roles with no structural input. Everything is
    derived from `VerbCore.predictedSubjectTheta`. -/
def lexicalistAccount : LinkingTheory VerbCore Unit where
  compatible := fun _ => [()]
  predict := fun v () pos =>
    match pos with
    | .subject => v.predictedSubjectTheta
    | _ => none  -- currently only predicts subject

end Theories.Interfaces.SyntaxSemantics.VoiceTheta
