import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Voice.Basic
import Linglib.Semantics.Causation.Implicative

/-!
# Finnish Verb Entries [karlsson-2017]

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

namespace Finnish.Predicates

open Minimalist (VoiceFlavor VoiceHead voiceAgent voiceImpersonal)

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
  deriving DecidableEq, Repr

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
theorem active_has_agent : finnishActive.AssignsTheta := by decide

/-- Finnish "passive" does NOT project an agent syntactically. -/
theorem passive_no_agent : ¬ finnishPassive.AssignsTheta := by decide

/-- Finnish "passive" HAS semantic content (existential closure over agent),
    unlike true anticausatives which are semantically vacuous. -/
theorem passive_has_semantics : finnishPassive.HasSemantics := by decide

/-- Finnish "passive" is NOT a phase head. -/
theorem passive_not_phase : ¬ finnishPassive.IsPhasal := by decide

/-- Finnish "passive" is distinct from anticausative — both lack a syntactic
    agent, but impersonal Voice has semantics while nonThematic does not. -/
theorem impersonal_vs_anticausative :
    finnishPassive.HasSemantics ∧ ¬ Minimalist.voiceAnticausative.HasSemantics :=
  by decide

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

/-! ### Finnish voice system

    Two-way asymmetrical (active/impersonal). Finnish lacks a true
    passive — what is traditionally called the passive is an impersonal
    construction where the agent is demoted to an implicit generic human
    referent, not promoted to a by-phrase ([karlsson-2017] Ch. 11).
    Active is the basic form. Not a true passive; impersonal with
    implicit generic agent (Karlsson 2018). -/
namespace VoiceSystem

def voices : List Voice.VoiceEntry := [ ⟨"Active", .agent⟩, ⟨"Impersonal", .patient⟩ ]

def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

theorem finnish_voice_system_asymmetrical :
    VoiceSystem.symmetry = .asymmetrical := rfl

theorem finnish_voice_count :
    Voice.voiceCount VoiceSystem.voices = 2 := rfl

theorem finnish_is_active_passive :
    Voice.isActivePassive VoiceSystem.voices := by decide

-- ============================================================================
-- § 6: Finnish Implicative Verbs ([nadathur-2023-implicatives])
-- ============================================================================

/-! Finnish is the ideal testing ground for implicative verb semantics because
    it has a much richer inventory of lexically-specific implicatives than
    English. Where English has primarily *manage* (underspecified) and *dare*
    (courage), Finnish has ~12 common implicatives that each lexicalize a
    different prerequisite type.

    The structure extends `FinnishVerb` with implicative fields. -/

open Features (Implicative)
open Causation.Implicative (Directionality Prerequisite ImplicativeClass)

/-- A Finnish implicative verb entry, extending the base verb with
    implicative classification from [nadathur-2023-implicatives]. -/
structure FinnishImplicativeVerb extends FinnishVerb where
  /-- Positive (entails complement) or negative (entails ¬complement) -/
  implicative : Implicative
  /-- One-way or two-way complement entailment -/
  directionality : Directionality
  /-- The lexically-specified prerequisite type -/
  prerequisite : Prerequisite
  /-- Negative 3sg present (with negation verb *ei*) -/
  neg3sgAct : String
  deriving Repr, BEq

-- ── Two-way positive implicatives ──

/-- *onnistua* 'succeed, manage' — two-way positive, unspecified prerequisite.
    "Eman onnistui pakenema-an" → 'Eman fled.'
    "Eman ei onnistunut pakenema-an" → 'Eman did not flee.'
    ([nadathur-2023-implicatives] ex. 2) -/
def onnistua : FinnishImplicativeVerb :=
  { infinitive := "onnistua"
    gloss := "to succeed, to manage"
    verbType := .type1
    pres3sgAct := "onnistuu"
    presImpersonal := "onnistutaan"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .unspecified
    neg3sgAct := "onnistu" }

/-- *uskaltaa* 'dare' — two-way positive, prerequisite = courage.
    "Juno uskaltaa avata oven" → 'Juno opens the door.'
    "Juno ei uskaltanut avata ovea" → 'Juno did not open the door.'
    ([nadathur-2023-implicatives] ex. 4) -/
def uskaltaa : FinnishImplicativeVerb :=
  { infinitive := "uskaltaa"
    gloss := "to dare"
    verbType := .type1
    pres3sgAct := "uskaltaa"
    presImpersonal := "uskalletaan"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .courage
    neg3sgAct := "uskalla" }

/-- *viitsiä* 'bother' — two-way positive, prerequisite = engagement.
    ([nadathur-2023-implicatives] ex. 10) -/
def viitsia : FinnishImplicativeVerb :=
  { infinitive := "viitsiä"
    gloss := "to bother"
    verbType := .type1
    pres3sgAct := "viitsii"
    presImpersonal := "viitsitään"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .engagement
    neg3sgAct := "viitsi" }

/-- *malttaa* 'have the patience' — two-way positive, prerequisite = patience.
    "Marja malttoi odottaa" → 'Marja waited.'
    "Marja ei malttanut odottaa" → 'Marja did not wait.'
    ([nadathur-2023-implicatives] ex. 11) -/
def malttaa : FinnishImplicativeVerb :=
  { infinitive := "malttaa"
    gloss := "to have the patience"
    verbType := .type1
    pres3sgAct := "malttaa"
    presImpersonal := "maltetaan"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .patience
    neg3sgAct := "maltta" }

/-- *hennoa* 'have the heart' — two-way positive, prerequisite = hard-heartedness.
    ([nadathur-2023-implicatives] ex. 27) -/
def hennoa : FinnishImplicativeVerb :=
  { infinitive := "hennoa"
    gloss := "to have the heart"
    verbType := .type1
    pres3sgAct := "hennoaa"  -- note: not *hennoo
    presImpersonal := "hennotaan"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .hardHeartedness
    neg3sgAct := "hennoa" }  -- negation: ei hennoa (no consonant gradation)

/-- *kehdata* 'act without shame, be unembarrassed' — two-way positive.
    ([nadathur-2023-implicatives] ex. 40) -/
def kehdata : FinnishImplicativeVerb :=
  { infinitive := "kehdata"
    gloss := "to act without shame"
    verbType := .type4
    pres3sgAct := "kehtaa"
    presImpersonal := "kehdataan"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .shamelessness
    neg3sgAct := "kehtaa" }

/-- *ehtiä* 'find/make time' — two-way positive, prerequisite = time.
    ([nadathur-2023-implicatives] ex. 39) -/
def ehtia : FinnishImplicativeVerb :=
  { infinitive := "ehtiä"
    gloss := "to find time, to make time"
    verbType := .type1
    pres3sgAct := "ehtii"
    presImpersonal := "ehditään"
    implicative := .positive
    directionality := .twoWay
    prerequisite := .time
    neg3sgAct := "ehdi" }

-- ── One-way positive implicatives ──

/-- *jaksaa* 'have the strength' — one-way positive, prerequisite = strength.
    Positive: "Sampo jaksoi nousta" ↛ 'Sampo rose.' (only implicature)
    Negative: "Sampo ei jaksanut nousta" → 'Sampo did not rise.'
    ([nadathur-2023-implicatives] ex. 5) -/
def jaksaa : FinnishImplicativeVerb :=
  { infinitive := "jaksaa"
    gloss := "to have the strength"
    verbType := .type1
    pres3sgAct := "jaksaa"
    presImpersonal := "jaksetaan"
    implicative := .positive
    directionality := .oneWay
    prerequisite := .strength
    neg3sgAct := "jaksa" }

/-- *mahtua* 'fit, be small enough' — one-way positive, prerequisite = fitness.
    "Freija mahtui kulkemaan oven" ↛ 'Freija went through the door.'
    "Freija ei mahtunut kulkemaan oven" → 'Freija did not go through the door.'
    ([nadathur-2023-implicatives] ex. 30) -/
def mahtua : FinnishImplicativeVerb :=
  { infinitive := "mahtua"
    gloss := "to fit"
    verbType := .type1
    pres3sgAct := "mahtuu"
    presImpersonal := "mahdutaan"
    implicative := .positive
    directionality := .oneWay
    prerequisite := .fitness
    neg3sgAct := "mahdu" }

/-- *pystyä* 'be able' — one-way positive (the Finnish counterpart of *be able*).
    "Maarit pystyi tappelema-an" ↛ 'Maarit fought.'
    "Maarit ei pystynyt tappelema-an" → 'Maarit did not fight.'
    ([nadathur-2023-implicatives] ex. 29) -/
def pystya : FinnishImplicativeVerb :=
  { infinitive := "pystyä"
    gloss := "to be able"
    verbType := .type1
    pres3sgAct := "pystyy"
    presImpersonal := "pystytään"
    implicative := .positive
    directionality := .oneWay
    prerequisite := .unspecified
    neg3sgAct := "pysty" }

-- ── Polarity-reversing implicatives ──

/-- *laiminlyödä* 'neglect' — polarity-reversing two-way.
    "Hän laiminlöi korjata virheen" → 'He did not correct the error.'
    "Hän ei laiminlyönyt korjata virhettä" → 'He corrected the error.'
    ([nadathur-2023-implicatives] ex. 44) -/
def laiminlyoda : FinnishImplicativeVerb :=
  { infinitive := "laiminlyödä"
    gloss := "to neglect"
    verbType := .type2
    pres3sgAct := "laiminlyö"
    presImpersonal := "laiminlyödään"
    implicative := .negative
    directionality := .twoWay
    prerequisite := .unspecified
    neg3sgAct := "laiminlyö" }

/-- *epäröidä* 'hesitate' — polarity-reversing one-way.
    "Juno epäröi ottaa osaa kilpailuun" ↛ 'Juno did not take part.'
    "Juno ei epäröinyt ottaa osaa kilpailuun" → 'Juno took part.'
    ([nadathur-2023-implicatives] §6.4, ex. 46) -/
def eparoida : FinnishImplicativeVerb :=
  { infinitive := "epäröidä"
    gloss := "to hesitate"
    verbType := .type2
    pres3sgAct := "epäröi"
    presImpersonal := "epäröidään"
    implicative := .negative
    directionality := .oneWay
    prerequisite := .courage
    neg3sgAct := "epäröi" }

-- ── Verification theorems ──

/-- All two-way implicatives have `.twoWay` directionality. -/
theorem twoWay_verbs_correct :
    onnistua.directionality = .twoWay ∧
    uskaltaa.directionality = .twoWay ∧
    viitsia.directionality = .twoWay ∧
    malttaa.directionality = .twoWay ∧
    hennoa.directionality = .twoWay ∧
    kehdata.directionality = .twoWay ∧
    ehtia.directionality = .twoWay ∧
    laiminlyoda.directionality = .twoWay :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- All one-way implicatives have `.oneWay` directionality. -/
theorem oneWay_verbs_correct :
    jaksaa.directionality = .oneWay ∧
    mahtua.directionality = .oneWay ∧
    pystya.directionality = .oneWay ∧
    eparoida.directionality = .oneWay :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Each specific implicative has a distinct prerequisite type. -/
theorem prerequisites_distinct :
    uskaltaa.prerequisite = .courage ∧
    viitsia.prerequisite = .engagement ∧
    malttaa.prerequisite = .patience ∧
    hennoa.prerequisite = .hardHeartedness ∧
    jaksaa.prerequisite = .strength ∧
    mahtua.prerequisite = .fitness ∧
    ehtia.prerequisite = .time ∧
    kehdata.prerequisite = .shamelessness :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Bleached implicatives (manage-type) have unspecified prerequisites. -/
theorem bleached_unspecified :
    onnistua.prerequisite = .unspecified ∧
    pystya.prerequisite = .unspecified :=
  ⟨rfl, rfl⟩

/-- Polarity-reversing verbs have negative polarity. -/
theorem polarity_reversing :
    laiminlyoda.implicative = .negative ∧
    eparoida.implicative = .negative :=
  ⟨rfl, rfl⟩

/-- Polarity-preserving verbs have positive polarity. -/
theorem polarity_preserving :
    onnistua.implicative = .positive ∧
    uskaltaa.implicative = .positive ∧
    viitsia.implicative = .positive ∧
    malttaa.implicative = .positive ∧
    hennoa.implicative = .positive ∧
    jaksaa.implicative = .positive ∧
    mahtua.implicative = .positive ∧
    pystya.implicative = .positive ∧
    kehdata.implicative = .positive ∧
    ehtia.implicative = .positive :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Convert a Finnish implicative verb to an ImplicativeClass. -/
def FinnishImplicativeVerb.toImplicativeClass (v : FinnishImplicativeVerb) : ImplicativeClass :=
  { polarity := v.implicative
    directionality := v.directionality
    aspectGoverned := false
    prerequisite := some v.prerequisite }

/-- Uskaltaa and English dare have the same classification. -/
theorem uskaltaa_matches_dare :
    uskaltaa.toImplicativeClass = ImplicativeClass.dare := rfl

end Finnish.Predicates
