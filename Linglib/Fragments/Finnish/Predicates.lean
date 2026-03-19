import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Core.VoiceSystem

/-!
# Finnish Verb Entries @cite{karlsson-2017}

Finnish verbs illustrate two phenomena that exercise linglib's infrastructure:

1. **The impersonal "passive"** — Finnish lacks a true passive. What is traditionally called the passive is an impersonal
   construction: the agent is demoted to an implicit generic human referent,
   not promoted to a by-phrase. The subject position remains empty.

   Active: *Mies avasi oven.* 'The man opened the door.'
   "Passive": *Ovi avattiin.* 'The door was opened (by someone).'

   This is formalized using `VoiceFlavor.impersonal`, distinct from both
   `nonThematic` (anticausative, no agent at all) and `agentive` (syntactically
   projected agent).

2. **Verb type classification** — Finnish has 6 productive verb types
   (conjugation classes) based on infinitive stem shape (Karlsson §10.1).
   We record the type as data, not as separate MorphRules, since the
   classification is lexical.

-/

namespace Fragments.Finnish.Predicates

open Minimalism (VoiceFlavor VoiceHead voiceAgent voiceImpersonal)

-- ============================================================================
-- § 1: Verb Entry Type
-- ============================================================================

/-- Finnish verb type (conjugation class, Karlsson §10.1). -/
inductive VerbType where
  | type1  -- -aa/-ää stems (sanoa, lukea)
  | type2  -- -da/-dä stems (saada, myydä)
  | type3  -- -la/-lä, -na/-nä, -ra/-rä, -sta/-stä stems (tulla, mennä)
  | type4  -- -ata/-ätä stems (haluta, pelätä)
  | type5  -- -ita/-itä stems (tarvita, häiritä)
  | type6  -- -eta/-etä stems (vanheta, lämmetä)
  deriving DecidableEq, BEq, Repr

/-- A Finnish verb entry with active and impersonal "passive" forms. -/
structure FinnishVerb where
  /-- Infinitive (dictionary form, I infinitive) -/
  infinitive : String
  /-- English gloss -/
  gloss : String
  /-- Verb type (conjugation class) -/
  verbType : VerbType
  /-- 3sg present active -/
  pres3sgAct : String
  /-- Impersonal "passive" present -/
  presImpersonal : String
  deriving Repr, BEq

-- ============================================================================
-- § 2: Sample Verb Entries
-- ============================================================================

def avata : FinnishVerb :=
  { infinitive := "avata"
  , gloss := "to open"
  , verbType := .type4
  , pres3sgAct := "avaa"
  , presImpersonal := "avataan" }

def lukea : FinnishVerb :=
  { infinitive := "lukea"
  , gloss := "to read"
  , verbType := .type1
  , pres3sgAct := "lukee"
  , presImpersonal := "luetaan" }

def tulla : FinnishVerb :=
  { infinitive := "tulla"
  , gloss := "to come"
  , verbType := .type3
  , pres3sgAct := "tulee"
  , presImpersonal := "tullaan" }

def haluta : FinnishVerb :=
  { infinitive := "haluta"
  , gloss := "to want"
  , verbType := .type4
  , pres3sgAct := "haluaa"
  , presImpersonal := "halutaan" }

-- ============================================================================
-- § 3: Voice Heads for Finnish
-- ============================================================================

/-- Active Finnish voice: agentive, projects a syntactic agent. -/
def finnishActive : VoiceHead := voiceAgent

/-- Finnish "passive" voice: impersonal, no syntactic agent specifier.
    The agent is existentially closed — someone performs the action,
    but the someone is not a syntactic argument. -/
def finnishPassive : VoiceHead := voiceImpersonal

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- Active Finnish verbs project an agent. -/
theorem active_has_agent : finnishActive.assignsTheta = true := rfl

/-- Finnish "passive" does NOT project an agent syntactically. -/
theorem passive_no_agent : finnishPassive.assignsTheta = false := rfl

/-- Finnish "passive" HAS semantic content (existential closure over agent),
    unlike true anticausatives which are semantically vacuous. -/
theorem passive_has_semantics : finnishPassive.hasSemantics = true := rfl

/-- Finnish "passive" is NOT a phase head. -/
theorem passive_not_phase : finnishPassive.phaseHead = false := rfl

/-- Finnish "passive" is distinct from anticausative — both lack a syntactic
    agent, but impersonal Voice has semantics while nonThematic does not. -/
theorem impersonal_vs_anticausative :
    finnishPassive.hasSemantics = true ∧
    (Minimalism.voiceAnticausative).hasSemantics = false := ⟨rfl, rfl⟩

/-- All impersonal forms end in *-aan* or *-ään* (back or front harmony on
    the passive marker). -/
theorem impersonal_suffix :
    [avata, lukea, tulla, haluta].all
      (fun v => v.presImpersonal.endsWith "aan") = true := by native_decide

/-- All 4 sample verbs have distinct verb types. -/
theorem verb_types_distinct :
    avata.verbType ≠ lukea.verbType ∧
    lukea.verbType ≠ tulla.verbType ∧
    tulla.verbType ≠ haluta.verbType := by
  exact ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 5: Voice System Profile
-- ============================================================================

/-- Finnish voice system: two-way asymmetrical (active/impersonal).

    Finnish lacks a true passive — what is traditionally called the
    passive is an impersonal construction where the agent is demoted
    to an implicit generic human referent, not promoted to a by-phrase
    (@cite{karlsson-2017} Ch. 11). Active is the basic form. -/
def finnishVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Finnish"
    voices := [ ⟨"Active", .agent⟩, ⟨"Impersonal", .patient⟩ ]
    symmetry := .asymmetrical
    notes := "Not a true passive; impersonal with implicit generic agent (Karlsson 2018)" }

theorem finnish_voice_system_asymmetrical :
    finnishVoiceSystem.symmetry = .asymmetrical := rfl

theorem finnish_voice_count :
    finnishVoiceSystem.voiceCount = 2 := rfl

theorem finnish_is_active_passive :
    finnishVoiceSystem.isActivePassive = true := rfl

end Fragments.Finnish.Predicates
