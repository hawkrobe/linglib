import Linglib.Core.VoiceSystem
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Indonesian Voice System
@cite{sneddon-1996} @cite{arka-2003}

Indonesian distinguishes three productive voice prefixes on verbs:

- **meN-** (agent voice): the canonical active — subject = agent, object = patient.
  Allomorphs: *me-*, *mem-*, *men-*, *meny-*, *meng-*, *menge-*.
- **di-** (patient voice / passive): subject = patient, agent optionally
  expressed via *oleh* 'by' PP or postverbal DP.
- **ber-** (middle voice): detransitivizing prefix producing reflexive,
  dispositional/passive, anticausative, and incorporation readings
  (@cite{beavers-udayana-2022}).

There is also an unmarked object voice (OV) where the agent is a
preverbal pronoun/DP and the patient follows the bare root, but we
focus on the prefixed forms here.

## Parametric decomposition

Under the Minimalist analysis of @cite{alexiadou-schfer-2015}, the three
voices occupy distinct positions in the ±D / ±λx parameter space:

| Voice | ±D | ±λx | Notes |
|-------|----|-----|-------|
| meN-  | +D | +λx (arg) | Active: projects agent specifier |
| di-   | +D | −λx | Passive: specifier is weak implicit *e*[−D] |
| ber-  | ? | ? | Underspecified: both params determined by context |

The key property of *ber-* is underspecification: the same morpheme
produces agentive-like behavior (incorporation middles, where the
agent is the surface subject) and expletive-like behavior
(dispositional middles, where the patient is the surface subject).
-/

namespace Fragments.Indonesian.VoiceSystem

open Interfaces (VoiceEntry PivotTarget VoiceSystemProfile VoiceSystemSymmetry)
open Minimalism (VoiceParams ExternalArgSemantics VoiceFlavor)

-- ============================================================================
-- § 1: Voice Entries (descriptive, theory-neutral)
-- ============================================================================

/-- Agent voice *meN-*: promotes agent to subject (pivot). -/
def menVoice : VoiceEntry :=
  { name := "meN-", promotes := .agent }

/-- Patient voice *di-*: promotes patient to subject. -/
def diVoice : VoiceEntry :=
  { name := "di-", promotes := .patient }

/-- Middle voice *ber-*: promotes patient to subject in dispositional/
    passive/anticausative readings; promotes agent in incorporation
    readings. Default pivot target is patient (the more common case). -/
def berVoice : VoiceEntry :=
  { name := "ber-", promotes := .patient }

/-- Indonesian voice system profile: three-way asymmetrical system.
    *meN-* is the unmarked active; *di-* and *ber-* are marked. -/
def indonesianVoiceSystem : VoiceSystemProfile :=
  { language := "Indonesian"
  , voices := [menVoice, diVoice, berVoice]
  , symmetry := .asymmetrical
  , notes := "Sneddon 1996: 56–67; Arka 2003. OV (unmarked object voice) omitted." }

-- ============================================================================
-- § 2: Parametric Decomposition (Minimalist analysis)
-- ============================================================================

/-- *meN-* parameters: active Voice[+D, +λx].
    Projects a full DP external argument and introduces agent semantics. -/
def menParams : VoiceParams :=
  { selectsSpecifier := some true
  , extArgSemantics := some .thematicArgument }

/-- *di-* parameters: passive Voice[+D, −λx].
    Projects a specifier (weak implicit argument *e*[−D]) but introduces
    no semantic agent — the agent is entailed to exist but is syntactically
    defective (@cite{alexiadou-schfer-2015}: 132, 141–142). -/
def diParams : VoiceParams :=
  { selectsSpecifier := some true
  , extArgSemantics := some .expletive }

/-- *ber-* parameters: underspecified Voice[±D, ±λx].
    Neither ±D nor ±λx is fixed — the actual setting is determined by
    independent argument realization strategies (incorporation vs.
    functional application) and lexical semantic/pragmatic factors
    (@cite{beavers-udayana-2022}: §3). -/
def berParams : VoiceParams :=
  { selectsSpecifier := none
  , extArgSemantics := none }

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- The Indonesian voice system has exactly three voices. -/
theorem voice_count : indonesianVoiceSystem.voiceCount = 3 := rfl

/-- The system promotes both agent and patient roles. -/
theorem promotes_agent : indonesianVoiceSystem.promotesRole .agent = true := rfl
theorem promotes_patient : indonesianVoiceSystem.promotesRole .patient = true := rfl

/-- *meN-* is fully specified; *ber-* is not. -/
theorem men_fully_specified : menParams.isFullySpecified = true := rfl
theorem di_fully_specified : diParams.isFullySpecified = true := rfl
theorem ber_underspecified : berParams.isFullySpecified = false := rfl

/-- *meN-* maps to the same cell as Minimalist agentive Voice. -/
theorem men_is_agentive :
    menParams = VoiceFlavor.agentive.toParams := rfl

/-- *di-* maps to the same cell as Minimalist passive/anticausative Voice. -/
theorem di_is_passive_cell :
    diParams = VoiceFlavor.passive.toParams := rfl

/-- *ber-* is compatible with EVERY named VoiceFlavor — the defining
    property of an underspecified voice morpheme. -/
theorem ber_compatible_with_all (f : VoiceFlavor) :
    berParams.isCompatibleWith f.toParams = true := by
  cases f <;> rfl

end Fragments.Indonesian.VoiceSystem
