import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking
import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry

/-!
# Severing Account of θ-Role Assignment

@cite{kratzer-1996} @cite{schaefer-2008} @cite{alexiadou-schaefer-2015} @cite{levin-2004} @cite{goldberg-1995}

The **severing** account holds that the Voice head —
not the verb root — determines which theta role the external argument
gets. The verb root is category-neutral; argument structure comes from
the functional sequence.

Note: this is sometimes called the "constructionist" position, but that
term is better reserved for Construction Grammar, which makes a different (stronger) claim. The Minimalist Voice
analysis is specifically Kratzer's **severing** of the external argument.

## The prediction

`VoiceFlavor.thetaRole` maps each Voice flavor to the theta role
it assigns. The current typology has
these θ-assigning flavors:

- Voice_AG → agent
- Voice_CAUSE → stimulus
- Voice_REFL → agent (with reflexive binding; @cite{wood-2015})
- Voice_EXP → experiencer (@cite{wood-2015})

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
open Semantics.Causation.Psych (CausalSource)
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
  | .agentive     => some .agent
  | .causer       => some .stimulus
  | .antipassive  => some .agent  -- agent is still present, just with ABS case
  | .reflexive    => some .agent  -- agent that binds internal argument (@cite{wood-2015})
  | .experiencer  => some .experiencer  -- subject-experiencer (@cite{wood-2015})
  | .nonThematic  => none
  | .expletive    => none
  | .impersonal   => none
  | .passive      => none

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

    - `causalSource.isSome` → Voice_CAUSE (Class II psych, @cite{kim-2024})
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
-- § 3. Gradient Voice compatibility (@cite{levin-2004})
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

/-- Lexicalist prediction of the external argument's theta role, based
    solely on verb-internal properties (@cite{levin-1993},
    @cite{rappaport-hovav-levin-1998}).

    The cascade mirrors traditional linking rules:
    - raising / weather → no external role
    - external causal source → stimulus (Class II psych, @cite{kim-2024})
    - attitude builder or factive presupposition → experiencer
    - occasion sense (manage-to) → experiencer
    - Levin class flinch / learn → experiencer
    - unaccusative / measure → theme
    - default → agent -/
def _root_.Core.Verbs.VerbCore.predictedSubjectTheta (v : VerbCore) : Option ThetaRole :=
  if v.controlType == .raising then none
  else if v.levinClass == some .weather then none
  else if v.causalSource.isSome then some .stimulus
  else if v.attitude.isSome then some .experiencer
  else if v.factivePresup && v.attitude.isNone then some .experiencer
  else if v.senseTag == .occasion then some .experiencer
  else if v.levinClass == some .flinch then some .experiencer
  else if v.levinClass == some .learn then some .experiencer
  else if v.unaccusative then some .theme
  else if v.levinClass == some .measure then some .theme
  else some .agent

/-- The lexicalist account (@cite{levin-1993}, Rappaport @cite{rappaport-hovav-levin-1998})
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
