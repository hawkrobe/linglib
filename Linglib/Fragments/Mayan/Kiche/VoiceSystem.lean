import Linglib.Core.VoiceSystem
import Linglib.Fragments.Mayan.Kiche.Agreement

/-!
# K'iche' Voice System Fragment @cite{mondloch-2017}

The five transitive voice alternations of K'iche', following
@cite{mondloch-2017} Lessons 15–22, 26–30.

## Voice Inventory

K'iche' has five voices for transitive verbs (plus an instrumental
voice not covered in the grammar):

1. **Active Voice** (Lessons 15–18, 26–27): Subject (A), verb, and
   object (P) are all expressed. Voice marker: **-j** for derived
   transitive verbs (DTVs), **-Ø** for radical transitive verbs (RTVs).
   Template: `aspect + P(SetB) + A(SetA) + root + voice`.

2. **Simple Passive** (Lessons 19–20, 28–29): P is promoted to subject
   (triggers Set B); A is demoted to an oblique (introduced by
   *rumaal/kumaal* 'by'). Voice marker: **-x** (DTVs), **-Vtaj**
   (RTVs). Template: `aspect + S(SetB) + root + passive`.

3. **Absolutive Antipassive** (Lesson 21): A is kept as subject
   (triggers Set B as if intransitive); P is suppressed entirely.
   Voice marker: **-n** (DTVs). Verb conjugates like an intransitive.
   Template: `aspect + S(SetB) + root + antipass`.

4. **Agent-Focus Antipassive** (Lessons 22, 30): The subject (A) is
   focused/emphasized. P triggers Set B, A appears as a separated
   pronoun before the verb. Voice marker: **-n** (DTVs), **-Vk** (RTVs).
   This is the voice used for **subject extraction** (wh-questions about
   the agent), which is why subject extraction triggers Agent Focus
   morphology rather than *wi*.

5. **Completed Passive** (Lessons 20, 29): Like Simple Passive but with
   completed aspect. Voice marker: **-taaj** (DTVs for completed
   aspect only).

## Verb Classes

- **Derived Transitive Verbs (DTVs)**: Polysyllabic roots ending in
  vowels (e.g., *kuna* 'to cure', *tzuku* 'to look for').
- **Radical Transitive Verbs (RTVs)**: Monosyllabic roots ending in
  consonants (e.g., *b'an* 'to do', *ch'ay* 'to hit').

## Aspect Markers

- **Incomplete**: k- (ka- before consonant clusters)
- **Completed**: x-

## Connection to Extraction Morphology

Agent Focus Antipassive (voice 4) is the morphological strategy used for
**subject extraction** in K'iche'. When the agent is extracted via
Ā-movement (e.g., 'Who bought it?'), the verb appears in Agent Focus
voice with the **-n** or **-Vk** marker, not with the fronting particle *wi*.
This is why `subjectExtraction.wiLicensed = false` in
`ExtractionMorphology.lean` — subject extraction uses Agent Focus, not
*wi*.
-/

namespace Fragments.Mayan.Kiche

-- ============================================================================
-- § 1: Verb Classes
-- ============================================================================

/-- K'iche' transitive verb classes., Lesson 15. -/
inductive TransVerbClass where
  /-- Derived: polysyllabic roots ending in vowels. -/
  | derived
  /-- Radical: monosyllabic roots ending in consonants. -/
  | radical
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Voice Alternations
-- ============================================================================

/-- The five transitive voices of K'iche'.,
    Lessons 15–22, 26–30. -/
inductive KicheVoice where
  /-- Active Voice: A and P both expressed. -/
  | active
  /-- Simple Passive: P promoted to subject, A demoted to oblique. -/
  | simplePassive
  /-- Absolutive Antipassive: A is subject, P suppressed. -/
  | absolutiveAntipassive
  /-- Agent-Focus Antipassive: A is focused/extracted. -/
  | agentFocus
  /-- Completed Passive (distinct morphology from Simple Passive in
      completed aspect). -/
  | completedPassive
  deriving DecidableEq, Repr

/-- All five voices. -/
def allVoices : List KicheVoice :=
  [.active, .simplePassive, .absolutiveAntipassive, .agentFocus, .completedPassive]

-- ============================================================================
-- § 3: Voice Markers
-- ============================================================================

/-- The voice marker suffix for derived transitive verbs (DTVs).
   : Active = -j (Lesson 15), Simple Passive = -x
    (Lesson 19), Antipassive = -n (Lesson 21), Agent Focus = -n
    (Lesson 22), Completed Passive = -taaj (Lesson 20). -/
def dtvVoiceMarker : KicheVoice → String
  | .active                 => "-j"
  | .simplePassive          => "-x"
  | .absolutiveAntipassive  => "-n"
  | .agentFocus             => "-n"
  | .completedPassive       => "-taaj"

/-- The voice marker suffix for radical transitive verbs (RTVs).
   : Active = Ø (Lesson 26), Simple Passive = -Vtaj
    (Lesson 28, where V is a copy of the root vowel), Agent Focus = -Vk
    (Lesson 30). -/
def rtvVoiceMarker : KicheVoice → String
  | .active                 => "Ø"
  | .simplePassive          => "-Vtaj"
  | .absolutiveAntipassive  => "-n"
  | .agentFocus             => "-Vk"
  | .completedPassive       => "-Vtaj"

-- ============================================================================
-- § 4: Aspect Markers
-- ============================================================================

/-- K'iche' aspect markers., Lesson 9. -/
inductive Aspect where
  | incomplete  -- k- (ka- before clusters)
  | completed   -- x-
  deriving DecidableEq, Repr

/-- The morphological form of the aspect marker.
   , Lesson 9: k- (ka-) for incomplete, x- for
    completed. -/
def aspectMarker : Aspect → String
  | .incomplete => "k-"
  | .completed  => "x-"

-- ============================================================================
-- § 5: Morphological Templates
-- ============================================================================

/-- The transitive active voice template:
    aspect + P(Set B) + A(Set A) + root + voice marker.
   , Lesson 15. -/
structure ActiveVerbForm where
  aspect : Aspect
  object : PhiFeatures  -- P: cross-referenced by Set B
  subject : PhiFeatures -- A: cross-referenced by Set A
  root : String
  verbClass : TransVerbClass
  deriving Repr

/-- The passive voice template:
    aspect + S(Set B) + root + passive marker.
    The agent appears as an oblique (rumaal/kumaal).
   , Lesson 19. -/
structure PassiveVerbForm where
  aspect : Aspect
  subject : PhiFeatures  -- promoted P, cross-referenced by Set B
  root : String
  verbClass : TransVerbClass
  deriving Repr

/-- The antipassive voice template:
    aspect + S(Set B) + root + antipassive marker.
    P is suppressed. Verb conjugates like an intransitive.
   , Lesson 21. -/
structure AntipassiveVerbForm where
  aspect : Aspect
  subject : PhiFeatures  -- A, cross-referenced by Set B (as intransitive)
  root : String
  verbClass : TransVerbClass
  deriving Repr

-- ============================================================================
-- § 6: Argument Realization per Voice
-- ============================================================================

/-- Does this voice realize A (the transitive agent) as a full
    agreement-bearing argument? In Active and Agent Focus, yes. In
    passives and Absolutive Antipassive, A is either demoted (oblique)
    or absent. -/
def KicheVoice.realizesAgent : KicheVoice → Bool
  | .active      => true
  | .agentFocus  => true   -- A is focused, realized as separated pronoun
  | _            => false

/-- Does this voice realize P (the transitive patient) as a full
    agreement-bearing argument? In Active and passives, yes. In
    antipassives, P is suppressed or demoted. -/
def KicheVoice.realizesPatient : KicheVoice → Bool
  | .active          => true
  | .simplePassive   => true   -- P is promoted to subject
  | .completedPassive => true
  | _                => false

/-- Is the verb in this voice conjugated like an intransitive
    (only Set B agreement, no Set A)?
    Passives and antipassives both conjugate intransitively.
   : Lesson 19 (passive = "like intransitive"),
    Lesson 21 (antipassive = "exactly as Simple Intransitive Verbs"). -/
def KicheVoice.conjugatesIntransitively : KicheVoice → Bool
  | .active     => false  -- Set A + Set B
  | .agentFocus => false  -- separated pronoun + Set B
  | _           => true   -- passives, antipassive: Set B only

-- ============================================================================
-- § 7: Agent Focus and Subject Extraction
-- ============================================================================

/-- Agent Focus is the voice used for subject extraction in K'iche'.
    When 'who' questions target the agent, the verb appears in Agent
    Focus, not Active Voice. This is why *wi* is not licensed for
    subject extraction — Agent Focus morphology is used instead.
   , Lesson 22; @cite{mendes-ranero-2021}, §2. -/
def subjectExtractionVoice : KicheVoice := .agentFocus

/-- Agent Focus Antipassive shares the same marker as Absolutive
    Antipassive for DTVs (-n), but their functions are distinct.
   , Lesson 22 notes: "In spite of the confusingly
    similar structure between the two voices, their meanings are quite
    different." -/
theorem af_marker_eq_antip_marker :
    dtvVoiceMarker .agentFocus = dtvVoiceMarker .absolutiveAntipassive := rfl

/-- For RTVs, Agent Focus and Absolutive Antipassive have DIFFERENT
    markers: -Vk vs -n. -/
theorem rtv_af_marker_neq_antip :
    rtvVoiceMarker .agentFocus ≠ rtvVoiceMarker .absolutiveAntipassive := by
  decide

-- ============================================================================
-- § 8: Voice System Profile
-- ============================================================================

/-- K'iche' voice system profile. Five voices, asymmetrical (Active
    is the basic form). -/
def kicheVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "K'iche'"
  , voices :=
    [ ⟨"Active Voice", .agent⟩
    , ⟨"Simple Passive", .patient⟩
    , ⟨"Completive Passive", .patient⟩
    , ⟨"Absolutive Antipassive", .agent⟩
    , ⟨"Agent Focus Antipassive", .agent⟩ ]
  , symmetry := .asymmetrical
  , notes := "5 voices (+ instrumental, not covered); Active is basic " ++
             "(Mondloch 2017); Agent Focus used for subject extraction" }

-- ============================================================================
-- § 9: Voice System Theorems
-- ============================================================================

/-- K'iche' has 5 voices. -/
theorem kiche_voice_count : kicheVoiceSystem.voiceCount = 5 := rfl

/-- K'iche' voice system is asymmetrical (Active is basic). -/
theorem kiche_asymmetrical :
    kicheVoiceSystem.symmetry = .asymmetrical := rfl

/-- K'iche' is NOT a simple active/passive system (it has 5 voices,
    not 2). -/
theorem kiche_not_simple_active_passive :
    ¬ kicheVoiceSystem.isActivePassive := by decide

-- ============================================================================
-- § 10: DTV Voice Marker Verification
-- ============================================================================

theorem dtv_active_marker : dtvVoiceMarker .active = "-j" := rfl
theorem dtv_passive_marker : dtvVoiceMarker .simplePassive = "-x" := rfl
theorem dtv_antip_marker : dtvVoiceMarker .absolutiveAntipassive = "-n" := rfl
theorem dtv_af_marker : dtvVoiceMarker .agentFocus = "-n" := rfl
theorem dtv_comppass_marker : dtvVoiceMarker .completedPassive = "-taaj" := rfl

-- ============================================================================
-- § 11: Negation Template — Lesson 13
-- ============================================================================

/-- K'iche' negation uses a circumfixal pattern: **na...taj/ta**.
    The first element *na* precedes the negated constituent; the second
    element *taj* (or *ta* before verbs) follows it.
   , Lesson 13. -/
structure Negation where
  proclitic : String := "na"
  enclitic : String
  deriving DecidableEq, Repr

/-- Negation of nonverbal predicates (pronouns, nouns, adjectives,
    adverbs, prepositions): na...taj. -/
def negNonverbal : Negation := { enclitic := "taj" }

/-- Negation of verbal predicates: na...ta. -/
def negVerbal : Negation := { enclitic := "ta" }

/-- Both negation forms share the proclitic *na*. -/
theorem neg_same_proclitic :
    negNonverbal.proclitic = negVerbal.proclitic := rfl

-- ============================================================================
-- § 12: Word Order — Lesson 9
-- ============================================================================

/-- K'iche' basic word order for intransitive clauses with noun
    subjects is Verb-Subject (VS).
   , Lesson 9: "the preferred word order appears
    to be: verb-subject." -/
inductive BasicWordOrder where
  | VS   -- Verb-Subject (intransitive)
  | VOS  -- Verb-Object-Subject (transitive active)
  | VS_passive  -- Verb-Subject (passive, with oblique agent)
  deriving DecidableEq, Repr

/-- Intransitive basic word order is verb-initial. -/
def intransitiveOrder : BasicWordOrder := .VS

/-- Transitive active basic word order is VOS. The object appears
    between the verb and the subject. -/
def transitiveOrder : BasicWordOrder := .VOS

end Fragments.Mayan.Kiche
