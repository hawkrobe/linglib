/-! # Complementation Typology (Noonan 2007)

Cross-linguistic data on complement types and complement-taking predicates (CTPs).

Based on:
- Noonan, M. (2007). Complementation. In T. Shopen (ed.), Language Typology
  and Syntactic Description, vol. 2, 2nd ed. Cambridge University Press.

## Key contributions

1. Six complement types attested cross-linguistically
2. Twelve CTP classes organized by semantics
3. Realis/irrealis split predicts complement type selection
4. Equi-deletion restricted to reduced complement types
5. Implicational hierarchy on complement type distribution
6. Negative raising data (fills a gap in linglib)
-/

namespace Phenomena.Complementation.Typology

/-! ## A. Complement types (Noonan 2007 §1) -/

/-- The six major complement types attested cross-linguistically.
    Ordered roughly from most to least "finite" (Noonan's "balanced" to "deranked"). -/
inductive NoonanCompType where
  | indicative     -- Finite clause with indicative mood marking
  | subjunctive    -- Finite clause with subjunctive/irrealis marking
  | paratactic     -- Juxtaposed clause, no subordinator
  | infinitive     -- Non-finite with "to" or equivalent
  | nominalized    -- Gerund / action nominal
  | participle     -- Participial complement
  deriving DecidableEq, Repr, BEq

/-! ## B. Complement-taking predicate classes (Noonan 2007 Table 2.1) -/

/-- Noonan's twelve CTP classes, organized by semantic contribution.

    The ordering follows Noonan's Table 2.1 from most to least "assertive":
    - Utterance/propAttitude/pretence: report/judge propositional content
    - Commentative/knowledge: evaluate/know propositional content
    - Perception: direct experience
    - Desiderative/manipulative/modal: irrealis orientation
    - Achievement/phasal: aspectual
    - Negative: negation as CTP -/
inductive CTPClass where
  | utterance       -- say, tell, report
  | propAttitude    -- believe, think, suppose
  | pretence        -- pretend, act as if
  | commentative    -- regret, be sorry
  | knowledge       -- know, realize, discover
  | perception      -- see, hear, feel
  | desiderative    -- want, wish, hope
  | manipulative    -- make, cause, persuade, order
  | modal           -- can, must, should
  | achievement     -- manage, fail, dare
  | phasal          -- start, stop, continue
  | negative        -- avoid, refrain, prevent
  deriving DecidableEq, Repr, BEq

/-! ## C. Reality status (Noonan 2007 §2.3) -/

/-- The fundamental realis/irrealis split that predicts complement type selection.
    Realis CTPs tend toward indicative; irrealis toward subjunctive/infinitive. -/
inductive RealityStatus where
  | realis    -- CTP asserts or presupposes complement truth
  | irrealis  -- CTP does not commit to complement truth
  deriving DecidableEq, Repr, BEq

/-- Reality status of each CTP class (Noonan 2007 Table 2.3). -/
def ctpRealityStatus : CTPClass → RealityStatus
  | .utterance    => .realis
  | .propAttitude => .realis
  | .pretence     => .irrealis
  | .commentative => .realis
  | .knowledge    => .realis
  | .perception   => .realis
  | .desiderative => .irrealis
  | .manipulative => .irrealis
  | .modal        => .irrealis
  | .achievement  => .irrealis
  | .phasal       => .realis
  | .negative     => .irrealis

/-! ## D. CTP data structure -/

/-- A cross-linguistic datum about a complement-taking predicate.

    Each datum records:
    - Language and verb identification
    - CTP class (Noonan Table 2.1)
    - Which complement types this verb allows in this language
    - Reality status (derived from CTP class, but overridable for exceptions)
    - Control/raising properties (Noonan §2.1-2.2)
    - Negative raising (fills a gap in linglib) -/
structure CTPDatum where
  language : String
  verb : String
  ctpClass : CTPClass
  allowedCompTypes : List NoonanCompType
  realityStatus : RealityStatus
  hasEquiDeletion : Bool
  hasRaising : Bool
  hasNegativeRaising : Bool
  deriving DecidableEq, Repr, BEq

/-! ## E. Cross-linguistic data

### English

English attests all six complement types (Noonan 2007 §1.1):
- Indicative: "John said that he was tired"
- Subjunctive: "I demand that he leave" (mandative)
- Paratactic: "John told Mary go away" (marginal)
- Infinitive: "John wants to leave"
- Nominalized: "John enjoys swimming"
- Participle: "I saw him leaving"
-/

def english_say : CTPDatum where
  language := "English"
  verb := "say"
  ctpClass := .utterance
  allowedCompTypes := [.indicative, .paratactic]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_tell : CTPDatum where
  language := "English"
  verb := "tell"
  ctpClass := .utterance
  allowedCompTypes := [.indicative, .infinitive]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_believe : CTPDatum where
  language := "English"
  verb := "believe"
  ctpClass := .propAttitude
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := true
  hasNegativeRaising := true

def english_think : CTPDatum where
  language := "English"
  verb := "think"
  ctpClass := .propAttitude
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := true

def english_regret : CTPDatum where
  language := "English"
  verb := "regret"
  ctpClass := .commentative
  allowedCompTypes := [.indicative, .nominalized]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_know : CTPDatum where
  language := "English"
  verb := "know"
  ctpClass := .knowledge
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_realize : CTPDatum where
  language := "English"
  verb := "realize"
  ctpClass := .knowledge
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_see : CTPDatum where
  language := "English"
  verb := "see"
  ctpClass := .perception
  allowedCompTypes := [.indicative, .infinitive, .participle]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_want : CTPDatum where
  language := "English"
  verb := "want"
  ctpClass := .desiderative
  allowedCompTypes := [.infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := true
  hasNegativeRaising := true

def english_hope : CTPDatum where
  language := "English"
  verb := "hope"
  ctpClass := .desiderative
  allowedCompTypes := [.indicative, .infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def english_wish : CTPDatum where
  language := "English"
  verb := "wish"
  ctpClass := .desiderative
  allowedCompTypes := [.indicative, .subjunctive]
  realityStatus := .irrealis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_make : CTPDatum where
  language := "English"
  verb := "make"
  ctpClass := .manipulative
  allowedCompTypes := [.infinitive, .paratactic]
  realityStatus := .irrealis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def english_persuade : CTPDatum where
  language := "English"
  verb := "persuade"
  ctpClass := .manipulative
  allowedCompTypes := [.infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def english_manage : CTPDatum where
  language := "English"
  verb := "manage"
  ctpClass := .achievement
  allowedCompTypes := [.infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def english_stop : CTPDatum where
  language := "English"
  verb := "stop"
  ctpClass := .phasal
  allowedCompTypes := [.nominalized]
  realityStatus := .realis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def english_start : CTPDatum where
  language := "English"
  verb := "start"
  ctpClass := .phasal
  allowedCompTypes := [.nominalized, .infinitive]
  realityStatus := .realis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def english_continue : CTPDatum where
  language := "English"
  verb := "continue"
  ctpClass := .phasal
  allowedCompTypes := [.nominalized, .infinitive]
  realityStatus := .realis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

/-- ### Latin

Latin uses indicative/subjunctive split along the realis/irrealis line
(Noonan 2007 §1.3). -/

def latin_dicere : CTPDatum where
  language := "Latin"
  verb := "dicere"
  ctpClass := .utterance
  allowedCompTypes := [.indicative, .infinitive]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := true
  hasNegativeRaising := false

def latin_credere : CTPDatum where
  language := "Latin"
  verb := "credere"
  ctpClass := .propAttitude
  allowedCompTypes := [.infinitive]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := true
  hasNegativeRaising := false

def latin_velle : CTPDatum where
  language := "Latin"
  verb := "velle"
  ctpClass := .desiderative
  allowedCompTypes := [.subjunctive, .infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def latin_iubere : CTPDatum where
  language := "Latin"
  verb := "iubere"
  ctpClass := .manipulative
  allowedCompTypes := [.subjunctive, .infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

/-- ### Turkish

Turkish strongly favors nominalized complements (Noonan 2007 §1.4).
Key contrast: even realis CTPs use nominalized forms. -/

def turkish_sanmak : CTPDatum where
  language := "Turkish"
  verb := "sanmak"
  ctpClass := .propAttitude
  allowedCompTypes := [.nominalized, .indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def turkish_istemek : CTPDatum where
  language := "Turkish"
  verb := "istemek"
  ctpClass := .desiderative
  allowedCompTypes := [.nominalized, .infinitive]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def turkish_baslamak : CTPDatum where
  language := "Turkish"
  verb := "başlamak"
  ctpClass := .phasal
  allowedCompTypes := [.nominalized, .infinitive]
  realityStatus := .realis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

/-- ### Irish

Irish uses a finite/non-finite split with interesting paratactic patterns
(Noonan 2007 §1.5). -/

def irish_abair : CTPDatum where
  language := "Irish"
  verb := "abair"
  ctpClass := .utterance
  allowedCompTypes := [.indicative, .subjunctive]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def irish_ceap : CTPDatum where
  language := "Irish"
  verb := "ceap"
  ctpClass := .propAttitude
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

/-- ### Persian

Persian shows a clear subjunctive/indicative split along CTP lines
(Noonan 2007 §2.3). -/

def persian_goftan : CTPDatum where
  language := "Persian"
  verb := "goftan"
  ctpClass := .utterance
  allowedCompTypes := [.indicative, .subjunctive]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def persian_khastan : CTPDatum where
  language := "Persian"
  verb := "khastan"
  ctpClass := .desiderative
  allowedCompTypes := [.subjunctive]
  realityStatus := .irrealis
  hasEquiDeletion := false  -- Persian SUBJ pro-drop, not Noonan-equi
  hasRaising := false
  hasNegativeRaising := false

def persian_danestan : CTPDatum where
  language := "Persian"
  verb := "danestan"
  ctpClass := .knowledge
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

/-- ### Hindi-Urdu

Hindi-Urdu connects to existing Questions/Typology data.
Uses subjunctive complement with desideratives (Noonan 2007 §2.3). -/

def hindi_urdu_sochna : CTPDatum where
  language := "Hindi-Urdu"
  verb := "sochna"
  ctpClass := .propAttitude
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def hindi_urdu_jaanna : CTPDatum where
  language := "Hindi-Urdu"
  verb := "jaanna"
  ctpClass := .knowledge
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def hindi_urdu_chaahna : CTPDatum where
  language := "Hindi-Urdu"
  verb := "chaahna"
  ctpClass := .desiderative
  allowedCompTypes := [.subjunctive]
  realityStatus := .irrealis
  hasEquiDeletion := false  -- Hindi-Urdu has PRO-drop in SUBJ, not Noonan-equi
  hasRaising := false
  hasNegativeRaising := false

/-- ### Japanese

Japanese connects to existing Q-particle data.
Uses nominalized complements extensively. -/

def japanese_omou : CTPDatum where
  language := "Japanese"
  verb := "omou"
  ctpClass := .propAttitude
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def japanese_shiru : CTPDatum where
  language := "Japanese"
  verb := "shiru"
  ctpClass := .knowledge
  allowedCompTypes := [.indicative]
  realityStatus := .realis
  hasEquiDeletion := false
  hasRaising := false
  hasNegativeRaising := false

def japanese_hoshii : CTPDatum where
  language := "Japanese"
  verb := "hoshii"
  ctpClass := .desiderative
  allowedCompTypes := [.nominalized]
  realityStatus := .irrealis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

def japanese_hajimeru : CTPDatum where
  language := "Japanese"
  verb := "hajimeru"
  ctpClass := .phasal
  allowedCompTypes := [.nominalized, .infinitive]
  realityStatus := .realis
  hasEquiDeletion := true
  hasRaising := false
  hasNegativeRaising := false

/-! ## F. Data collections -/

def allEnglishCTPData : List CTPDatum := [
  english_say, english_tell, english_believe, english_think,
  english_regret, english_know, english_realize, english_see,
  english_want, english_hope, english_wish,
  english_make, english_persuade, english_manage,
  english_stop, english_start, english_continue
]

def allLatinCTPData : List CTPDatum := [
  latin_dicere, latin_credere, latin_velle, latin_iubere
]

def allTurkishCTPData : List CTPDatum := [
  turkish_sanmak, turkish_istemek, turkish_baslamak
]

def allIrishCTPData : List CTPDatum := [
  irish_abair, irish_ceap
]

def allPersianCTPData : List CTPDatum := [
  persian_goftan, persian_khastan, persian_danestan
]

def allHindiUrduCTPData : List CTPDatum := [
  hindi_urdu_sochna, hindi_urdu_jaanna, hindi_urdu_chaahna
]

def allJapaneseCTPData : List CTPDatum := [
  japanese_omou, japanese_shiru, japanese_hoshii, japanese_hajimeru
]

def allCTPData : List CTPDatum :=
  allEnglishCTPData ++ allLatinCTPData ++ allTurkishCTPData ++
  allIrishCTPData ++ allPersianCTPData ++ allHindiUrduCTPData ++
  allJapaneseCTPData

/-! ## G. Verified generalizations

### G1. Realis/irrealis split (Noonan 2007 Table 2.3)

Utterance, propAttitude, commentative, knowledge, perception, and phasal
CTPs are realis; desiderative, manipulative, modal, achievement, pretence,
and negative are irrealis.
-/

theorem realis_classes :
    ctpRealityStatus .utterance = .realis ∧
    ctpRealityStatus .propAttitude = .realis ∧
    ctpRealityStatus .commentative = .realis ∧
    ctpRealityStatus .knowledge = .realis ∧
    ctpRealityStatus .perception = .realis ∧
    ctpRealityStatus .phasal = .realis := by decide

theorem irrealis_classes :
    ctpRealityStatus .desiderative = .irrealis ∧
    ctpRealityStatus .manipulative = .irrealis ∧
    ctpRealityStatus .modal = .irrealis ∧
    ctpRealityStatus .achievement = .irrealis ∧
    ctpRealityStatus .pretence = .irrealis ∧
    ctpRealityStatus .negative = .irrealis := by decide

/-- Each datum's reality status matches the CTP class's default. -/
theorem reality_status_consistent :
    ∀ d ∈ allCTPData, d.realityStatus = ctpRealityStatus d.ctpClass := by
  decide

/-! ### G2. Equi-deletion restriction (Noonan 2007 §2.1)

Equi-deletion (subject deletion under coreference) only occurs with
reduced complement types (infinitive, nominalized), not with finite
complements (indicative, subjunctive).
-/

/-- Is this complement type "reduced" (non-finite)? -/
def NoonanCompType.isReduced : NoonanCompType → Bool
  | .infinitive => true
  | .nominalized => true
  | .participle => true
  | _ => false

/-- Equi-deletion only occurs when some allowed complement type is reduced. -/
theorem equi_requires_reduced :
    ∀ d ∈ allCTPData,
      d.hasEquiDeletion = true →
      d.allowedCompTypes.any NoonanCompType.isReduced = true := by
  decide

/-! ### G3. Negative raising data (fills gap in linglib)

Negative raising: "I don't think he left" ≈ "I think he didn't leave".
Only propAttitude and desiderative CTPs support it. Knowledge/commentative do not.

This is the first negative-raising data in linglib.
-/

/-- Negative raising verbs are exclusively propAttitude or desiderative. -/
theorem negative_raising_class_restriction :
    ∀ d ∈ allCTPData,
      d.hasNegativeRaising = true →
      d.ctpClass = .propAttitude ∨ d.ctpClass = .desiderative := by
  decide

/-- Knowledge CTPs never support negative raising. -/
theorem knowledge_no_negative_raising :
    ∀ d ∈ allCTPData,
      d.ctpClass = .knowledge → d.hasNegativeRaising = false := by
  decide

/-! ### G4. Implicational hierarchy (Noonan 2007 §2.4)

If a language uses indicative for desiderative CTPs, it also uses
indicative for propositional attitude CTPs. This is checked per-language. -/

/-- Does this language use indicative with desideratives? -/
def languageHasIndicativeDesiderative (data : List CTPDatum) (lang : String) : Bool :=
  data.any fun d =>
    d.language == lang && d.ctpClass == .desiderative &&
    d.allowedCompTypes.any (· == .indicative)

/-- Does this language use indicative with propAttitudes? -/
def languageHasIndicativePropAttitude (data : List CTPDatum) (lang : String) : Bool :=
  data.any fun d =>
    d.language == lang && d.ctpClass == .propAttitude &&
    d.allowedCompTypes.any (· == .indicative)

/-- Implicational hierarchy per-language: if indicative desiderative exists,
    then indicative propAttitude also exists. -/
theorem indicative_hierarchy_english :
    languageHasIndicativeDesiderative allCTPData "English" = true →
    languageHasIndicativePropAttitude allCTPData "English" = true := by native_decide

theorem indicative_hierarchy_latin :
    languageHasIndicativeDesiderative allCTPData "Latin" = true →
    languageHasIndicativePropAttitude allCTPData "Latin" = true := by native_decide

theorem indicative_hierarchy_turkish :
    languageHasIndicativeDesiderative allCTPData "Turkish" = true →
    languageHasIndicativePropAttitude allCTPData "Turkish" = true := by native_decide

theorem indicative_hierarchy_irish :
    languageHasIndicativeDesiderative allCTPData "Irish" = true →
    languageHasIndicativePropAttitude allCTPData "Irish" = true := by native_decide

theorem indicative_hierarchy_persian :
    languageHasIndicativeDesiderative allCTPData "Persian" = true →
    languageHasIndicativePropAttitude allCTPData "Persian" = true := by native_decide

theorem indicative_hierarchy_hindi_urdu :
    languageHasIndicativeDesiderative allCTPData "Hindi-Urdu" = true →
    languageHasIndicativePropAttitude allCTPData "Hindi-Urdu" = true := by native_decide

theorem indicative_hierarchy_japanese :
    languageHasIndicativeDesiderative allCTPData "Japanese" = true →
    languageHasIndicativePropAttitude allCTPData "Japanese" = true := by native_decide

end Phenomena.Complementation.Typology
