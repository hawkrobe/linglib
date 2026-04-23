import Linglib.Phenomena.ArgumentStructure.VoiceSystem
import Linglib.Theories.Syntax.Minimalism.Voice

/-!
# Indonesian Voice System
@cite{sneddon-1996}

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

## Passive types (@cite{sneddon-1996} §3.27–3.32)

Indonesian has two structurally distinct passive constructions:
- **Type one** (§3.27): *di-*verb + (*oleh*) + agent. Agent is 3rd person or noun.
- **Type two** (§3.28): agent (pronoun) + bare verb. Agent is 1st/2nd person.

*dia*/*mereka* (3rd person pronouns) straddle both types (§3.29–3.30).
*ter-* verbs force type one for all agents, with obligatory *oleh* (§3.32).

## Parametric decomposition

Under the Minimalist analysis of @cite{alexiadou-schaefer-2015}, the three
voices occupy distinct positions in the ±D / ±λx parameter space:

| Voice | ±D | ±λx | Notes |
|-------|----|-----|-------|
| meN-  | +D | +λx (arg) | Active: projects agent specifier |
| di-   | +D | +∃x | Passive: agent existentially bound but semantically active |
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
  , notes := "Sneddon 1996: §1.167–177 (ber-), §1.265–275 (ter-), §3.26–40 (voice); Arka 2003. OV (unmarked object voice) omitted." }

-- ============================================================================
-- § 2: Parametric Decomposition (Minimalist analysis)
-- ============================================================================

/-- *meN-* parameters: active Voice[+D, +λx].
    Projects a full DP external argument and introduces agent semantics. -/
def menParams : VoiceParams :=
  { selectsSpecifier := some true
  , extArgSemantics := some .thematicArgument }

/-- *di-* parameters: Voice[+D, +∃x].
    Projects a specifier (weak implicit argument *e*[−D]) and introduces
    an existentially bound agent — the agent is entailed to exist but is
    syntactically defective (lacking [+D]).

    Unlike English passive Voice (which is [+D, −λx] in the
    @cite{alexiadou-schaefer-2015} typology), *di-*'s implicit argument is
    semantically active: it licenses *oleh* 'by' phrases and controls
    rationale clause PRO (@cite{beavers-udayana-2022}: §2.1). This places
    *di-* in the [+D, +∃x] cell — specifier selected, agent existentially
    bound — rather than the [+D, −λx] cell occupied by English passive
    and Romance anticausative SE. -/
def diParams : VoiceParams :=
  { selectsSpecifier := some true
  , extArgSemantics := some .thematicExistential }

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
theorem promotes_agent : indonesianVoiceSystem.promotesRole .agent := by decide
theorem promotes_patient : indonesianVoiceSystem.promotesRole .patient := by decide

/-- *meN-* is fully specified; *ber-* is not. -/
theorem men_fully_specified : menParams.isFullySpecified = true := rfl
theorem di_fully_specified : diParams.isFullySpecified = true := rfl
theorem ber_underspecified : berParams.isFullySpecified = false := rfl

/-- *meN-* maps to the same cell as Minimalist agentive Voice. -/
theorem men_is_agentive :
    menParams = VoiceFlavor.agentive.toParams := rfl

/-- *di-* occupies the [+D, +∃x] cell — a specifier that introduces an
    existentially bound participant. This is distinct from English passive
    Voice [+D, −λx] and Finnish impersonal [−D, +∃x]. -/
theorem di_has_existential_agent :
    diParams.extArgSemantics = some .thematicExistential := rfl

theorem di_selects_specifier :
    diParams.selectsSpecifier = some true := rfl

/-- *ber-* is compatible with EVERY named VoiceFlavor — the defining
    property of an underspecified voice morpheme. -/
theorem ber_compatible_with_all (f : VoiceFlavor) :
    berParams.isCompatibleWith f.toParams = true := by
  cases f <;> rfl

-- ============================================================================
-- § 4: Passive Types (@cite{sneddon-1996} §3.27–3.32)
-- ============================================================================

/-- Indonesian has two structurally distinct passive constructions
    (@cite{sneddon-1996} §3.27–3.28, following Dardjowidjojo 1978).

    - **Type one** (§3.27): *di-*verb + (*oleh*) + agent.
      Subject (patient) + **di-**verb + (**oleh**) + Agent.
      Used when the agent is 3rd person, a noun, or unexpressed.
      Example: *Saya dijemput oleh dia.* 'I was met by him.'

    - **Type two** (§3.28): agent (pronoun) + bare verb.
      Subject (patient) + Agent (pronoun) + Verb.
      Used when the agent is a 1st or 2nd person pronoun.
      Example: *Dia kami jemput.* 'He was met by us.'
      With *aku*/*kamu*, bound forms *ku-*/*kau-* are used:
      *Buku ini sudah kubaca.* 'I've read this book.' -/
inductive PassiveType where
  /-- *di-*verb + (*oleh*) + agent. Verb retains *di-* prefix. -/
  | typeOne
  /-- Agent + bare verb. No prefix on verb; agent is preverbal. -/
  | typeTwo
  deriving DecidableEq, Repr

/-- Classification of the agent DP in a passive clause, determining
    which passive type(s) are available. Sneddon (§3.29) draws a
    2×2 diagram with "Box A" (type one agents) and "Box B" (type two
    agents); *dia* and *mereka* straddle both boxes.

    The key generalization: person determines type two eligibility
    (all pronouns can appear in type two), while type one requires
    the agent to be 3rd person or a full noun. -/
inductive AgentDP where
  /-- 1st person pronoun: *saya* (sg), *kami* (pl excl), *kita* (pl incl).
      Type two only. Bound form *ku-* for *aku* (§3.28). -/
  | firstPerson
  /-- 2nd person pronoun: *kamu*, *Anda*, etc.
      Type two only. Bound form *kau-* for *kamu* (§3.28). -/
  | secondPerson
  /-- 3rd person pronoun: *dia* (sg), *mereka* (pl).
      Both types available — straddles Box A and Box B (§3.29–3.30). -/
  | thirdPronoun
  /-- Full noun or proper name used as agent.
      Type one only (§3.29). But personal names and kinship terms
      used as pronoun substitutes (§3.31) allow type two. -/
  | noun
  /-- No agent expressed. Type one only (§3.27). -/
  | unexpressed
  deriving DecidableEq, Repr

/-- Whether passive type one (*di-*verb) is available for this agent.
    Type one requires the agent to be in "Box A": 3rd person (pronoun
    or noun), or absent (@cite{sneddon-1996} §3.27, §3.29). -/
def AgentDP.allowsTypeOne : AgentDP → Bool
  | .firstPerson => false
  | .secondPerson => false
  | .thirdPronoun => true
  | .noun => true
  | .unexpressed => true

/-- Whether passive type two (agent + bare verb) is available.
    Type two requires the agent to be a pronoun, in "Box B"
    (@cite{sneddon-1996} §3.28, §3.29). -/
def AgentDP.allowsTypeTwo : AgentDP → Bool
  | .firstPerson => true
  | .secondPerson => true
  | .thirdPronoun => true
  | .noun => false
  | .unexpressed => false

/-- Every agent allows at least one passive type. -/
theorem agent_has_passive (a : AgentDP) :
    a.allowsTypeOne || a.allowsTypeTwo = true := by
  cases a <;> rfl

/-- Only 3rd person pronouns allow BOTH types — they are the
    straddling case in Sneddon's diagram (§3.29–3.30). -/
theorem only_third_pronoun_allows_both :
    [AgentDP.firstPerson, .secondPerson, .thirdPronoun, .noun, .unexpressed].all
      (fun a => (a.allowsTypeOne && a.allowsTypeTwo) == (a == .thirdPronoun))
    = true := rfl

/-- 1st and 2nd person pronouns are type-two-only — type one with
    these agents is ungrammatical (@cite{sneddon-1996} §3.29 fn. 2). -/
theorem first_person_type_two_only :
    AgentDP.firstPerson.allowsTypeOne = false ∧
    AgentDP.firstPerson.allowsTypeTwo = true := ⟨rfl, rfl⟩
theorem second_person_type_two_only :
    AgentDP.secondPerson.allowsTypeOne = false ∧
    AgentDP.secondPerson.allowsTypeTwo = true := ⟨rfl, rfl⟩

/-- Nouns are type-one-only — they cannot appear in the preverbal
    agent position of type two (@cite{sneddon-1996} §3.29). -/
theorem noun_type_one_only :
    AgentDP.noun.allowsTypeOne = true ∧
    AgentDP.noun.allowsTypeTwo = false := ⟨rfl, rfl⟩

/-- Agentless passives use type one exclusively — there is no
    type two without an agent (@cite{sneddon-1996} §3.27). -/
theorem unexpressed_type_one_only :
    AgentDP.unexpressed.allowsTypeOne = true ∧
    AgentDP.unexpressed.allowsTypeTwo = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: ter- and Passive Type Interaction (@cite{sneddon-1996} §3.32)
-- ============================================================================

/-- Whether a voice prefix restricts passive type selection.
    *ter-* and *ke-...-an* verbs allow only passive type one, even with
    1st/2nd person agents — *oleh* becomes obligatory (§3.32).
    Regular *di-* verbs allow both types per the usual person rules. -/
inductive VoicePrefixConstraint where
  /-- Normal passive type selection rules apply. -/
  | unconstrained
  /-- Only passive type one available, regardless of agent person.
      Applies to *ter-* and *ke-...-an* verbs (§3.32). -/
  | typeOneOnly
  deriving DecidableEq, Repr

/-- *ter-* verbs force type one passive — the preverbal agent position
    of type two is unavailable (@cite{sneddon-1996} §3.32). -/
def terVoiceConstraint : VoicePrefixConstraint := .typeOneOnly

/-- Regular *di-* verbs have no constraint on passive type selection. -/
def diVoiceConstraint : VoicePrefixConstraint := .unconstrained

/-- The effective passive types available, given a voice prefix
    constraint and an agent DP.

    Under `.typeOneOnly` (ter- verbs, §3.32), type one is forced for
    ALL agents regardless of person — the normal person restriction
    on type one is overridden. *oleh* becomes obligatory when the
    agent is a pronoun. -/
def effectivePassiveTypes (c : VoicePrefixConstraint) (a : AgentDP) :
    List PassiveType :=
  match c with
  | .typeOneOnly => [.typeOne]
  | .unconstrained =>
    (if a.allowsTypeOne then [.typeOne] else []) ++
    (if a.allowsTypeTwo then [.typeTwo] else [])

/-- Under ter- constraint, even 1st person agents use type one —
    overriding the normal rule that 1st person → type two.
    *oleh* is obligatory (§3.32).
    Example: *Masalah itu belum terselesaikan oleh kami.*
    'We haven't yet been able to settle that matter.' (§1.272). -/
theorem ter_forces_type_one_for_first :
    effectivePassiveTypes .typeOneOnly .firstPerson = [.typeOne] := rfl

/-- ter- constraint forces type one for ALL agent types. -/
theorem ter_always_type_one (a : AgentDP) :
    effectivePassiveTypes .typeOneOnly a = [.typeOne] := by
  cases a <;> rfl

/-- Under no constraint, 3rd person pronouns get both types. -/
theorem unconstrained_third_pronoun_both :
    effectivePassiveTypes .unconstrained .thirdPronoun =
      [.typeOne, .typeTwo] := rfl

/-- Under no constraint, 1st person gets only type two. -/
theorem unconstrained_first_type_two :
    effectivePassiveTypes .unconstrained .firstPerson = [.typeTwo] := rfl

end Fragments.Indonesian.VoiceSystem
