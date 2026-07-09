import Linglib.Syntax.Voice.Basic
import Linglib.Fragments.Mayan.Kiche.Agreement

/-!
# K'iche' Voice System

The five transitive voice alternations of K'iche' (K'ichean Mayan),
following [mondloch-2017] Lessons 15–22, 26–30: active, simple passive,
absolutive antipassive, agent-focus antipassive, and completed passive.
Agent-Focus Antipassive is the voice used for subject extraction, which
is why an extracted agent triggers AF morphology rather than the fronting
particle *wi*.

## Main declarations

* `Kiche.KicheVoice`, `Kiche.allVoices`: the five transitive voices.
* `Kiche.dtvVoiceMarker`, `Kiche.rtvVoiceMarker`: voice-marker exponents
  for derived vs radical transitive verbs.
* `Kiche.ActiveVerbForm`, `Kiche.PassiveVerbForm`,
  `Kiche.AntipassiveVerbForm`: morphological templates per voice.
* `Kiche.KicheVoice.RealizesAgent`, `.RealizesPatient`,
  `.ConjugatesIntransitively`: argument-realization predicates per voice.
* `Kiche.subjectExtractionVoice`: Agent Focus as the subject-extraction
  voice.
* `Kiche.Negation`, `Kiche.negNonverbal`, `Kiche.negVerbal`: the
  na...taj/ta circumfixal negation.

## Implementation notes

Verb classes split derived transitives (DTVs: polysyllabic vowel-final
roots, e.g. *kuna* 'to cure') from radical transitives (RTVs:
monosyllabic consonant-final roots, e.g. *b'an* 'to do'), which take
different voice-marker allomorphs. Aspect is incomplete *k-* (*ka-*
before clusters) or completed *x-*. The passive demotes the agent to an
oblique introduced by *rumaal/kumaal* 'by'. An instrumental voice exists
but is not covered here. Agent-Focus Antipassive is the strategy for
subject extraction ([mondloch-2017] Lesson 22; [mendes-ranero-2021] §2),
so `subjectExtraction.wiLicensed = false` in `ExtractionMorphology.lean` —
the extracted agent takes AF morphology, not *wi*. The word-order profile
lives in `WordOrder.lean`; the transitive/intransitive/passive
conjugation contrast [mondloch-2017] draws (Lesson 9) is paper-specific
apparatus that nothing here consumes.
-/

namespace Kiche

/-! ### Verb classes -/

/-- K'iche' transitive verb classes ([mondloch-2017] Lesson 15). -/
inductive TransVerbClass where
  /-- Derived: polysyllabic roots ending in vowels. -/
  | derived
  /-- Radical: monosyllabic roots ending in consonants. -/
  | radical
  deriving DecidableEq, Repr

/-! ### Voice alternations -/

/-- The five transitive voices of K'iche' ([mondloch-2017]
    Lessons 15–22, 26–30). -/
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

/-! ### Voice markers -/

/-- Voice-marker suffix for derived transitive verbs (DTVs), per
    [mondloch-2017]: active *-j* (Lesson 15), simple passive *-x*
    (Lesson 19), antipassive *-n* (Lesson 21), Agent Focus *-n*
    (Lesson 22), completed passive *-taaj* (Lesson 20). -/
def dtvVoiceMarker : KicheVoice → String
  | .active                 => "-j"
  | .simplePassive          => "-x"
  | .absolutiveAntipassive  => "-n"
  | .agentFocus             => "-n"
  | .completedPassive       => "-taaj"

/-- Voice-marker suffix for radical transitive verbs (RTVs), per
    [mondloch-2017]: active Ø (Lesson 26), simple passive *-Vtaj*
    (Lesson 28, V copying the root vowel), Agent Focus *-Vk* (Lesson 30). -/
def rtvVoiceMarker : KicheVoice → String
  | .active                 => "Ø"
  | .simplePassive          => "-Vtaj"
  | .absolutiveAntipassive  => "-n"
  | .agentFocus             => "-Vk"
  | .completedPassive       => "-Vtaj"

/-! ### Aspect markers -/

/-- K'iche' aspect markers ([mondloch-2017] Lesson 9). -/
inductive Aspect where
  | incomplete  -- k- (ka- before clusters)
  | completed   -- x-
  deriving DecidableEq, Repr

/-- The morphological form of the aspect marker ([mondloch-2017]
    Lesson 9): k- (ka-) for incomplete, x- for completed. -/
def aspectMarker : Aspect → String
  | .incomplete => "k-"
  | .completed  => "x-"

/-! ### Morphological templates -/

/-- Transitive active voice template: aspect + P(Set B) + A(Set A) + root +
    voice marker ([mondloch-2017] Lesson 15). -/
structure ActiveVerbForm where
  aspect : Aspect
  object : PhiFeatures  -- P: cross-referenced by Set B
  subject : PhiFeatures -- A: cross-referenced by Set A
  root : String
  verbClass : TransVerbClass
  deriving Repr

/-- Passive voice template: aspect + S(Set B) + root + passive marker, with
    the agent as an oblique (rumaal/kumaal) ([mondloch-2017] Lesson 19). -/
structure PassiveVerbForm where
  aspect : Aspect
  subject : PhiFeatures  -- promoted P, cross-referenced by Set B
  root : String
  verbClass : TransVerbClass
  deriving Repr

/-- Antipassive voice template: aspect + S(Set B) + root + antipassive
    marker; P is suppressed and the verb conjugates like an intransitive
    ([mondloch-2017] Lesson 21). -/
structure AntipassiveVerbForm where
  aspect : Aspect
  subject : PhiFeatures  -- A, cross-referenced by Set B (as intransitive)
  root : String
  verbClass : TransVerbClass
  deriving Repr

/-! ### Argument realization per voice -/

/-- Does this voice realize A (the transitive agent) as a full
    agreement-bearing argument? In Active and Agent Focus, yes. In
    passives and Absolutive Antipassive, A is either demoted (oblique)
    or absent. -/
def KicheVoice.RealizesAgent : KicheVoice → Prop
  | .active      => True
  | .agentFocus  => True   -- A is focused, realized as separated pronoun
  | _            => False

instance : DecidablePred KicheVoice.RealizesAgent := fun v => by
  cases v <;> unfold KicheVoice.RealizesAgent <;> infer_instance

/-- Does this voice realize P (the transitive patient) as a full
    agreement-bearing argument? In Active and passives, yes. In
    antipassives, P is suppressed or demoted. -/
def KicheVoice.RealizesPatient : KicheVoice → Prop
  | .active          => True
  | .simplePassive   => True   -- P is promoted to subject
  | .completedPassive => True
  | _                => False

instance : DecidablePred KicheVoice.RealizesPatient := fun v => by
  cases v <;> unfold KicheVoice.RealizesPatient <;> infer_instance

/-- Is the verb in this voice conjugated like an intransitive
    (only Set B agreement, no Set A)?
    Passives and antipassives both conjugate intransitively.
    [mondloch-2017] Lesson 19 (passive = "like intransitive"),
    Lesson 21 (antipassive = "exactly as Simple Intransitive Verbs"). -/
def KicheVoice.ConjugatesIntransitively : KicheVoice → Prop
  | .active     => False  -- Set A + Set B
  | .agentFocus => False  -- separated pronoun + Set B
  | _           => True   -- passives, antipassive: Set B only

instance : DecidablePred KicheVoice.ConjugatesIntransitively := fun v => by
  cases v <;> unfold KicheVoice.ConjugatesIntransitively <;> infer_instance

/-! ### Agent Focus and subject extraction -/

/-- Agent Focus is the voice used for subject extraction in K'iche': 'who'
    questions targeting the agent take AF, not Active, which is why *wi* is
    not licensed for subject extraction ([mondloch-2017] Lesson 22;
    [mendes-ranero-2021] §2). -/
def subjectExtractionVoice : KicheVoice := .agentFocus

/-- Agent Focus and Absolutive Antipassive share the DTV marker *-n* but
    differ in function — [mondloch-2017] Lesson 22: "In spite of the
    confusingly similar structure between the two voices, their meanings
    are quite different." -/
theorem af_marker_eq_antip_marker :
    dtvVoiceMarker .agentFocus = dtvVoiceMarker .absolutiveAntipassive := rfl

/-- For RTVs, Agent Focus and Absolutive Antipassive have DIFFERENT
    markers: -Vk vs -n. -/
theorem rtv_af_marker_neq_antip :
    rtvVoiceMarker .agentFocus ≠ rtvVoiceMarker .absolutiveAntipassive := by
  decide

/-! ### Voice system profile -/

namespace VoiceSystem

/-- The five voices of K'iche'. -/
def voices : List Voice.VoiceEntry :=
  [ ⟨"Active Voice", .agent⟩
  , ⟨"Simple Passive", .patient⟩
  , ⟨"Completive Passive", .patient⟩
  , ⟨"Absolutive Antipassive", .agent⟩
  , ⟨"Agent Focus Antipassive", .agent⟩ ]

/-- K'iche' is asymmetrical — Active is the basic voice. -/
def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

/-! ### Voice system theorems -/

/-- K'iche' has 5 voices. -/
theorem kiche_voice_count : Voice.voiceCount Kiche.VoiceSystem.voices = 5 := rfl

/-- K'iche' voice system is asymmetrical (Active is basic). -/
theorem kiche_asymmetrical :
    Kiche.VoiceSystem.symmetry = .asymmetrical := rfl

/-- K'iche' is NOT a simple active/passive system (it has 5 voices,
    not 2). -/
theorem kiche_not_simple_active_passive :
    ¬ Voice.isActivePassive Kiche.VoiceSystem.voices := by decide

/-! ### DTV voice-marker verification -/

theorem dtv_active_marker : dtvVoiceMarker .active = "-j" := rfl
theorem dtv_passive_marker : dtvVoiceMarker .simplePassive = "-x" := rfl
theorem dtv_antip_marker : dtvVoiceMarker .absolutiveAntipassive = "-n" := rfl
theorem dtv_af_marker : dtvVoiceMarker .agentFocus = "-n" := rfl
theorem dtv_comppass_marker : dtvVoiceMarker .completedPassive = "-taaj" := rfl

/-! ### Negation template -/

/-- K'iche' circumfixal negation na...taj/ta: *na* precedes the negated
    constituent, *taj* (or *ta* before verbs) follows it ([mondloch-2017]
    Lesson 13). -/
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

end Kiche
