/-! # Complementation Typology

Cross-linguistic data on complement types, complement-taking predicates (CTPs),
and subordination strategies.

## Part I: CTP Typology (Noonan 2007)

Based on:
- Noonan, M. (2007). Complementation. In T. Shopen (ed.), Language Typology
  and Syntactic Description, vol. 2, 2nd ed. Cambridge University Press.

Key contributions:
1. Six complement types attested cross-linguistically
2. Twelve CTP classes organized by semantics
3. Realis/irrealis split predicts complement type selection
4. Equi-deletion restricted to reduced complement types
5. Implicational hierarchy on complement type distribution
6. Negative raising data (fills a gap in linglib)

## Part II: Subordination Strategies (WALS Chapters 94--95)

WALS data on the cross-linguistic distribution of subordination structures:
- **Ch 94**: Order of Adverbial Subordinator and Clause (Dryer 2013a)
- **Ch 95**: Relationship between OV Order and Adposition Order (Dryer 2013b)

Additional dimensions beyond WALS:
- Complementizer position (initial, final, none)
- Relative clause position (post-nominal, pre-nominal, internally headed, correlative)
- Purpose clause strategy (subjunctive, infinitive, nominalization, serial verb)

Key generalizations:
- Initial subordinators correlate with VO order; final subordinators with OV
- Post-nominal relative clauses are the global majority
- Pre-nominal RCs strongly correlate with OV order
- Complementizer position mirrors subordinator position
- SOV languages overwhelmingly use postpositions (Ch 95)
- Purpose clause strategy correlates with finiteness availability

## References

- Noonan, M. (2007). Complementation. In Shopen (ed.), Language Typology
  and Syntactic Description, vol. 2, 2nd ed. Cambridge University Press.
- Dryer, M. S. (2013a). Order of adverbial subordinator and clause. In
  Dryer & Haspelmath (eds.), WALS Online. https://wals.info/chapter/94
- Dryer, M. S. (2013b). Relationship between the order of object and verb
  and the order of adposition and noun phrase. In Dryer & Haspelmath
  (eds.), WALS Online. https://wals.info/chapter/95
- Diessel, H. (2013). Adverbial subordination. In Dryer & Haspelmath
  (eds.), WALS Online.
- Dixon, R. M. W. (2006). Complement clauses and complementation
  strategies in typological perspective. In Dixon & Aikhenvald (eds.),
  Complementation. Oxford University Press.
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

-- ============================================================================
-- Part II: Subordination Strategies (WALS Chapters 94--95)
-- ============================================================================

/-! ## H. WALS Chapter 94: Order of Adverbial Subordinator and Clause

Dryer (2013a) classifies languages by where the adverbial subordinator
(e.g., "because", "when", "if") appears relative to its clause. The
fundamental distinction is between word-level and suffix-level subordinators,
crossed with initial vs final position.

Sample: 611 languages.

The dominant pattern worldwide is clause-initial subordinator words (e.g.,
English "because he left"), which overwhelmingly correlates with VO order.
Final subordinator suffixes (e.g., Turkish "-dIgI icin") correlate with OV
order. This is one of the strongest head-direction correlations.
-/

/-- WALS Ch 94: How adverbial subordinators are positioned relative to
    their clause (Dryer 2013a).

    Five categories: subordinator word or suffix, initial or final position,
    plus a mixed/no-dominant category.
    - Initial word: English "because he left"
    - Final word: Hindi "kyonki" after clause (less common)
    - Initial suffix: extremely rare
    - Final suffix: Turkish "-dIgI icin" on the verb
    - Mixed: no single dominant pattern -/
inductive SubordinatorOrder where
  /-- Subordinator is a free word preceding the clause.
      E.g., English "because he left", Arabic "li'anna-hu ghaadara".
      The most common type worldwide (378/611 = 61.9%). -/
  | initialWord
  /-- Subordinator is a free word following the clause.
      E.g., Japanese "kare-ga kaetta kara" 'he-NOM returned because'.
      58/611 = 9.5%. -/
  | finalWord
  /-- Subordinator is a suffix preceding the clause. Extremely rare.
      7/611 = 1.1%. -/
  | initialSuffix
  /-- Subordinator is a suffix on the verb at the end of the clause.
      E.g., Turkish "-dIgI icin" 'because of V-NMZ'.
      54/611 = 8.8%. -/
  | finalSuffix
  /-- Mixed or no dominant subordination pattern.
      114/611 = 18.7%. -/
  | mixed
  deriving DecidableEq, BEq, Repr

/-- A single row in a WALS frequency table: a category label and its count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- Sum of counts in a WALS table. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (λ acc c => acc + c.count) 0

/-- Chapter 94 distribution: subordinator order (N = 611).
    Counts from Dryer (2013a), WALS Online, Ch 94. -/
def ch94Counts : List WALSCount :=
  [ ⟨"Initial subordinator word", 378⟩
  , ⟨"Final subordinator word", 58⟩
  , ⟨"Initial subordinator suffix", 7⟩
  , ⟨"Final subordinator suffix", 54⟩
  , ⟨"Mixed", 114⟩ ]

/-- Ch 94 total: 611 languages. -/
theorem ch94_total : WALSCount.totalOf ch94Counts = 611 := by native_decide

/-! ## I. WALS Chapter 95: OV Order and Adposition Order

Dryer (2013b) examines the correlation between verb-object order and
adposition type. This is one of the strongest head-direction correlations
in typology: OV languages overwhelmingly use postpositions, and VO languages
overwhelmingly use prepositions.

Sample: 981 languages.

The harmonic patterns (VO+prepositions, OV+postpositions) account for
926/981 = 94.4% of languages. The disharmonic patterns (VO+postpositions,
OV+prepositions) are extremely rare.
-/

/-- WALS Ch 95: Four-way classification combining verb-object order
    with adposition type (Dryer 2013b).

    The two "harmonic" patterns (matching head direction) dominate;
    the two "disharmonic" patterns are rare. -/
inductive OVAdpositionType where
  /-- VO order with prepositions (head-initial harmony).
      E.g., English "in the house", "sees the cat".
      454/981 = 46.3%. -/
  | voPrep
  /-- OV order with postpositions (head-final harmony).
      E.g., Japanese "neko-o miru", "ie-ni" (house-in).
      472/981 = 48.1%. -/
  | ovPostp
  /-- VO order with postpositions (disharmonic).
      E.g., some Austronesian languages. Very rare: 14/981 = 1.4%. -/
  | voPostp
  /-- OV order with prepositions (disharmonic).
      E.g., some Iranian languages. Rare: 41/981 = 4.2%. -/
  | ovPrep
  deriving DecidableEq, BEq, Repr

/-- Chapter 95 distribution: OV order × adposition type (N = 981).
    Counts from Dryer (2013b), WALS Online, Ch 95. -/
def ch95Counts : List WALSCount :=
  [ ⟨"VO & Prepositions", 454⟩
  , ⟨"OV & Postpositions", 472⟩
  , ⟨"VO & Postpositions", 14⟩
  , ⟨"OV & Prepositions", 41⟩ ]

/-- Ch 95 total: 981 languages. -/
theorem ch95_total : WALSCount.totalOf ch95Counts = 981 := by native_decide

/-! ## J. Additional Subordination Dimensions

Beyond the WALS chapters, three further dimensions characterize how
languages handle subordination: complementizer position, relative clause
position, and purpose clause strategy. These dimensions interact with
the subordinator order in systematic ways.
-/

/-- Position of the complementizer (the subordinating morpheme introducing
    a complement clause, e.g., English "that").

    The complementizer position strongly mirrors the subordinator order
    from WALS Ch 94: languages with initial subordinators tend to have
    initial complementizers, and vice versa. -/
inductive ComplementizerPosition where
  /-- Complementizer precedes the clause.
      E.g., English "that he left", Arabic "'inna-hu ghaadara". -/
  | initial
  /-- Complementizer follows the clause.
      E.g., Japanese "kare-ga kaetta to", Korean "ku-ka tteonass-ta-ko". -/
  | final
  /-- No overt complementizer; complementation via juxtaposition or
      verb morphology. E.g., Mandarin serial verb constructions. -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Position of the relative clause with respect to the head noun.

    WALS Ch 90 (Dryer 2013) documents the cross-linguistic distribution.
    Post-nominal is the global majority, but pre-nominal dominates in
    East and Central Asia. -/
inductive RelativeClausePosition where
  /-- RC follows the head noun (post-nominal).
      E.g., English "the man [who left]", Arabic "ar-rajul [alladhi ghaadara]".
      The most common type worldwide. -/
  | postNominal
  /-- RC precedes the head noun (pre-nominal).
      E.g., Japanese "[kaetta] hito" '[left] person',
      Mandarin "[zou-le de] ren" '[left DE] person'.
      Strongly correlated with OV order. -/
  | preNominal
  /-- Head noun appears inside the RC (internally headed).
      E.g., Bambara, Navajo. Rare. -/
  | internallyHeaded
  /-- A correlative construction: RC appears in one clause, head noun
      resumed by a pronoun in the main clause.
      E.g., Hindi "jo aadmii aayaa, vo lambaa hai"
      'which man came, he tall is'. -/
  | correlative
  deriving DecidableEq, BEq, Repr

/-- Strategy for expressing purpose clauses ("in order to V").

    The purpose clause strategy correlates with finiteness availability:
    languages with productive infinitives use infinitive purpose clauses,
    while languages lacking infinitives use subjunctive, nominalization,
    or serial verb constructions (Dixon 2006, Noonan 2007). -/
inductive PurposeClauseStrategy where
  /-- Purpose clause uses subjunctive/irrealis mood.
      E.g., Greek "gia na fiji" 'for SUBJ leave.3SG'. -/
  | subjunctive
  /-- Purpose clause uses infinitive.
      E.g., English "to leave", German "um zu gehen". -/
  | infinitive
  /-- Purpose clause uses a nominalized verb form.
      E.g., Turkish "git-mek icin" 'go-NMZ for'. -/
  | nominalization
  /-- Purpose expressed via serial verb construction.
      E.g., Yoruba, many West African and Oceanic languages. -/
  | serialVerb
  deriving DecidableEq, BEq, Repr

/-! ## K. Language Profile Structure -/

/-- A language's subordination profile combining all five dimensions.

    Each profile records:
    - WALS Ch 94: subordinator order
    - WALS Ch 95 (derived): OV-adposition correlation type
    - Complementizer position
    - Relative clause position
    - Purpose clause strategy
    - Basic word order (for cross-referencing with WordOrder/Typology)
    - ISO 639-3 code -/
structure SubordinationProfile where
  language : String
  iso : String := ""
  /-- Ch 94: order of adverbial subordinator and clause. -/
  subordinatorOrder : SubordinatorOrder
  /-- Ch 95: OV order × adposition type. -/
  ovAdposition : OVAdpositionType
  /-- Complementizer position (initial, final, or none). -/
  compPosition : ComplementizerPosition
  /-- Relative clause position. -/
  rcPosition : RelativeClausePosition
  /-- Purpose clause strategy. -/
  purposeStrategy : PurposeClauseStrategy
  /-- Basic word order label for cross-referencing. -/
  basicOrder : String := ""
  /-- Notes on the subordination system. -/
  notes : String := ""
  deriving Repr

/-! ## L. Language Profiles

Typologically diverse sample covering all major word-order types and
subordination strategies. Each profile is documented with the key
properties that distinguish it.
-/

/-- English: canonical VO language with initial subordinators and
    complementizers, post-nominal relative clauses, and infinitive purpose
    clauses. The prototypical head-initial subordination profile.
    - "because he left" (initial subordinator word)
    - "I know [that he left]" (initial complementizer)
    - "the man [who left]" (post-nominal RC)
    - "he came [to help]" (infinitive purpose) -/
def subEnglish : SubordinationProfile :=
  { language := "English"
  , iso := "eng"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "SVO"
  , notes := "Prototypical head-initial subordination" }

/-- Japanese: canonical OV language with final subordinators and
    complementizers, pre-nominal relative clauses, and nominalized
    purpose clauses. The prototypical head-final subordination profile.
    - "kare-ga kaetta kara" (final subordinator word)
    - "kare-ga kaetta to" (final complementizer "to")
    - "[kaetta] hito" (pre-nominal RC, no relative pronoun)
    - "tabe-ru tame-ni" (nominalization purpose: eat-NMZ for-DAT) -/
def subJapanese : SubordinationProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , subordinatorOrder := .finalWord
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Prototypical head-final subordination; no relative pronouns" }

/-- Turkish: OV language with subordinator suffixes on the verb, no overt
    complementizer (nominalized complements), pre-nominal relatives, and
    nominalized purpose clauses.
    - "gel-digi icin" (subordinator suffix: come-NMZ for)
    - "[gel-en] adam" (pre-nominal RC: come-PTCP man)
    - "git-mek icin" (nominalization purpose: go-INF for) -/
def subTurkish : SubordinationProfile :=
  { language := "Turkish"
  , iso := "tur"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .none
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Suffixal subordination; no complementizer; nominalized complements" }

/-- Hindi-Urdu: OV language with initial subordinator words (unusual for OV),
    correlative relative clauses (a South Asian areal feature), and
    subjunctive purpose clauses.
    - "kyonki vo gayaa" (initial subordinator word "because")
    - "ki vo gayaa" (initial complementizer "ki")
    - "jo aadmii aayaa, vo lambaa hai" (correlative RC)
    - "jaane ke liye" (infinitive purpose: go-INF GEN for) -/
def subHindiUrdu : SubordinationProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , subordinatorOrder := .initialWord
  , ovAdposition := .ovPostp
  , compPosition := .initial
  , rcPosition := .correlative
  , purposeStrategy := .infinitive
  , basicOrder := "SOV"
  , notes := "OV + initial subordinator (disharmonic); correlative RCs (South Asian areal)" }

/-- Mandarin Chinese: SVO language with no overt complementizer (or sentence-
    final particle "de"), pre-nominal relative clauses (unusual for VO), and
    serial verb purpose clauses.
    - Pre-nominal RC despite VO: "[zou-le de] ren" (left-PERF DE person)
    - Serial verb purpose: "lai bang ni" 'come help you'
    - Mixed headedness: head-initial VP but head-final NP -/
def subMandarin : SubordinationProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .none
  , rcPosition := .preNominal
  , purposeStrategy := .serialVerb
  , basicOrder := "SVO"
  , notes := "Mixed headedness: VO but pre-nominal RC; serial verb purpose clauses" }

/-- Arabic (Modern Standard): VSO language with initial subordinators
    and complementizers, post-nominal relative clauses, and subjunctive
    purpose clauses.
    - "li'anna-hu ghaadara" (initial subordinator "because")
    - "'anna-hu ghaadara" (initial complementizer)
    - "ar-rajul [alladhi ghaadara]" (post-nominal RC)
    - "li-ya-dhus" (subjunctive purpose: for-3MSG-enter.SUBJ) -/
def subArabic : SubordinationProfile :=
  { language := "Arabic (MSA)"
  , iso := "arb"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "VSO"
  , notes := "VSO with consistent head-initial subordination" }

/-- Korean: rigid OV language with final subordinators and complementizers,
    pre-nominal relative clauses, and nominalized purpose clauses.
    Very similar to Japanese.
    - "ku-ka tteonass-ki ttaemune" (final subordinator: he-NOM left-NMZ because)
    - "ku-ka tteonass-ta-ko" (final complementizer "-ko")
    - "[ttonass-ten] saram" (pre-nominal RC)
    - "ka-gi wihae" (nominalization purpose: go-NMZ for) -/
def subKorean : SubordinationProfile :=
  { language := "Korean"
  , iso := "kor"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Head-final like Japanese; suffixal subordination" }

/-- Irish: VSO language with initial subordinators and complementizers,
    post-nominal relative clauses, and subjunctive purpose clauses.
    Celtic VSO languages are consistently head-initial.
    - "mar gur imigh se" (initial subordinator "because")
    - "go bhfuil" (initial complementizer "go")
    - "an fear [a d'imigh]" (post-nominal RC) -/
def subIrish : SubordinationProfile :=
  { language := "Irish"
  , iso := "gle"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "VSO"
  , notes := "Celtic VSO; consistently head-initial" }

/-- Swahili: SVO language with initial subordinators and complementizers,
    post-nominal relative clauses, and subjunctive purpose clauses.
    - "kwa sababu alikwenda" (initial subordinator "because")
    - "kwamba alikwenda" (initial complementizer "that")
    - "mtu [ambaye alikwenda]" (post-nominal RC) -/
def subSwahili : SubordinationProfile :=
  { language := "Swahili"
  , iso := "swh"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "SVO"
  , notes := "Bantu SVO; consistent head-initial subordination" }

/-- Persian (Farsi): SOV language with initial subordinators (disharmonic
    for an OV language), initial complementizer "ke", post-nominal relative
    clauses (also disharmonic), and subjunctive purpose clauses.
    - "chon raft" (initial subordinator "because")
    - "ke raft" (initial complementizer "that")
    - "mard-i [ke raft]" (post-nominal RC, disharmonic for OV)
    - "baraye raftan" (infinitive purpose) -/
def subPersian : SubordinationProfile :=
  { language := "Persian"
  , iso := "fas"
  , subordinatorOrder := .initialWord
  , ovAdposition := .ovPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "SOV"
  , notes := "OV but head-initial subordination (disharmonic); Ch 95 OV+Prepositions" }

/-- German: V2 in main clauses, SOV in embedded; mixed subordination
    pattern with initial subordinators and complementizers.
    - "weil er ging" (initial subordinator "because")
    - "dass er ging" (initial complementizer "that")
    - "der Mann, [der ging]" (post-nominal RC) -/
def subGerman : SubordinationProfile :=
  { language := "German"
  , iso := "deu"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "V2/SOV"
  , notes := "V2 main clause; initial complementizer despite SOV embedded clauses" }

/-- Russian: SVO language with initial subordinators and complementizers,
    post-nominal relative clauses, and infinitive purpose clauses.
    - "potomu chto on ushel" (initial subordinator "because")
    - "chto on ushel" (initial complementizer "that")
    - "chelovek, [kotoryj ushel]" (post-nominal RC) -/
def subRussian : SubordinationProfile :=
  { language := "Russian"
  , iso := "rus"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "SVO"
  , notes := "SVO with consistent head-initial subordination" }

/-- Quechua (Southern): rigid SOV with final subordinator suffixes,
    no overt complementizer (nominalized complements), pre-nominal
    relative clauses, and nominalized purpose clauses.
    - "-pti" suffixed to verb (adverbial subordinator)
    - Nominalized complement: "ri-na-n-ta" 'go-NMZ-3-ACC'
    - "[hamu-q] runa" (pre-nominal RC: come-AG person) -/
def subQuechua : SubordinationProfile :=
  { language := "Quechua"
  , iso := "que"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .none
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Consistently head-final; suffixal subordination like Turkish" }

/-- Yoruba (Kwa): SVO language with initial subordinators, post-nominal
    relative clauses, and serial verb purpose clauses.
    - "toripe o lo" (initial subordinator "because")
    - "pe o lo" (initial complementizer "that")
    - "eniyan [ti o lo]" (post-nominal RC)
    - Serial verb purpose: "wa ran mi" 'come help me' -/
def subYoruba : SubordinationProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .serialVerb
  , basicOrder := "SVO"
  , notes := "SVO with serial verb purpose clauses (West African areal)" }

/-- Tagalog: V-initial (VSO/VOS) with initial subordinators, post-nominal
    relative clauses, and infinitive/nominalized purpose clauses.
    - "dahil umalis siya" (initial subordinator "because")
    - "na umalis siya" (initial linker/complementizer "na")
    - "ang tao [na umalis]" (post-nominal RC, with linker "na") -/
def subTagalog : SubordinationProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "VSO"
  , notes := "V-initial Austronesian; linker 'na' for complementation and RCs" }

/-- Basque: SOV language with final subordinator suffixes, no overt
    complementizer (nominalized complements), pre-nominal relative
    clauses, and nominalized purpose clauses.
    - "-lako" suffixed to verb (causal subordinator: because)
    - "-(e)la" suffixed to verb (complement clause marker)
    - "[etorri den] gizona" (pre-nominal RC: come AUX.REL man)
    - "-tzeko" nominalized purpose -/
def subBasque : SubordinationProfile :=
  { language := "Basque"
  , iso := "eus"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Language isolate; head-final subordination with suffixal markers" }

/-- Navajo: SOV language with final subordinators, pre-nominal relative
    clauses (internally headed also attested), and serial verb purpose
    clauses. Na-Dene family.
    - Subordination via enclitic particles on the verb
    - Internally headed RCs are attested
    - Serial verb purpose constructions -/
def subNavajo : SubordinationProfile :=
  { language := "Navajo"
  , iso := "nav"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .none
  , rcPosition := .internallyHeaded
  , purposeStrategy := .nominalization
  , basicOrder := "SOV"
  , notes := "Na-Dene; internally headed RCs attested; heavily suffixal" }

/-- Bambara: SOV language with initial subordinators and post-nominal
    relative clauses, and serial verb purpose clauses. One of the
    best-studied languages with internally headed RCs.
    - "a tagara bawo" (initial subordinator "because")
    - Internally headed RCs: a distinctive Mande feature
    - Serial verb purpose constructions -/
def subBambara : SubordinationProfile :=
  { language := "Bambara"
  , iso := "bam"
  , subordinatorOrder := .initialWord
  , ovAdposition := .ovPostp
  , compPosition := .initial
  , rcPosition := .internallyHeaded
  , purposeStrategy := .serialVerb
  , basicOrder := "SOV"
  , notes := "Mande language; canonical internally headed RCs" }

/-- Amharic: SOV language with final subordinators and complementizers,
    post-nominal relative clauses (unusual for an OV language), and
    subjunctive purpose clauses.
    - Subordinator suffixed to verb: "-s" (conditional), "-na" (when)
    - Post-nominal RC despite SOV: "ye-hedde sew" (REL-went man)
    - Subjunctive purpose: "le-yi-hed" 'for-3MSG-go.SUBJ' -/
def subAmharic : SubordinationProfile :=
  { language := "Amharic"
  , iso := "amh"
  , subordinatorOrder := .finalSuffix
  , ovAdposition := .ovPostp
  , compPosition := .final
  , rcPosition := .preNominal
  , purposeStrategy := .subjunctive
  , basicOrder := "SOV"
  , notes := "Semitic SOV; head-final subordination" }

/-- Malagasy: VOS language with initial subordinators and complementizers,
    post-nominal relative clauses, and infinitive purpose clauses.
    Austronesian with head-initial subordination.
    - "satria lasa izy" (initial subordinator "because")
    - "fa lasa izy" (initial complementizer "that")
    - "ny olona [izay lasa]" (post-nominal RC) -/
def subMalagasy : SubordinationProfile :=
  { language := "Malagasy"
  , iso := "mlg"
  , subordinatorOrder := .initialWord
  , ovAdposition := .voPrep
  , compPosition := .initial
  , rcPosition := .postNominal
  , purposeStrategy := .infinitive
  , basicOrder := "VOS"
  , notes := "VOS Austronesian; head-initial subordination" }

/-! ## M. Data Collections -/

/-- All subordination profiles in the sample. -/
def allSubProfiles : List SubordinationProfile :=
  [ subEnglish, subJapanese, subTurkish, subHindiUrdu, subMandarin
  , subArabic, subKorean, subIrish, subSwahili, subPersian
  , subGerman, subRussian, subQuechua, subYoruba, subTagalog
  , subBasque, subNavajo, subBambara, subAmharic, subMalagasy ]

/-- Sample size: 20 languages. -/
theorem sub_sample_size : allSubProfiles.length = 20 := by native_decide

/-! ## N. WALS Aggregate Total Verification -/

/-- Ch 94: initial subordinator words are the most common type (378/611). -/
theorem ch94_initial_word_most_common :
    (378 : Nat) > 58 ∧ (378 : Nat) > 7 ∧
    (378 : Nat) > 54 ∧ (378 : Nat) > 114 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Ch 95: harmonic patterns (VO+Prep, OV+Postp) dominate (926/981 = 94.4%). -/
theorem ch95_harmonic_dominant :
    454 + 472 > (454 + 472 + 14 + 41) * 9 / 10 := by
  native_decide

/-- Ch 95: OV+Postpositions is the single most common pairing. -/
theorem ch95_ov_postp_most_common :
    (472 : Nat) > 454 := by native_decide

/-- Ch 95: disharmonic patterns are rare (55/981 = 5.6%). -/
theorem ch95_disharmonic_rare :
    (14 + 41) * 100 < 981 * 6 := by native_decide

/-! ## O. Helper Predicates -/

/-- Does this profile have an initial subordinator (word or suffix)? -/
def SubordinationProfile.hasInitialSubordinator (p : SubordinationProfile) : Bool :=
  p.subordinatorOrder == .initialWord || p.subordinatorOrder == .initialSuffix

/-- Does this profile have a final subordinator (word or suffix)? -/
def SubordinationProfile.hasFinalSubordinator (p : SubordinationProfile) : Bool :=
  p.subordinatorOrder == .finalWord || p.subordinatorOrder == .finalSuffix

/-- Does this profile have VO order? -/
def SubordinationProfile.isVO (p : SubordinationProfile) : Bool :=
  p.ovAdposition == .voPrep || p.ovAdposition == .voPostp

/-- Does this profile have OV order? -/
def SubordinationProfile.isOV (p : SubordinationProfile) : Bool :=
  p.ovAdposition == .ovPostp || p.ovAdposition == .ovPrep

/-- Does this profile have pre-nominal RCs? -/
def SubordinationProfile.hasPreNominalRC (p : SubordinationProfile) : Bool :=
  p.rcPosition == .preNominal

/-- Does this profile have post-nominal RCs? -/
def SubordinationProfile.hasPostNominalRC (p : SubordinationProfile) : Bool :=
  p.rcPosition == .postNominal

/-- Count of profiles matching a predicate. -/
def countSubProfiles (pred : SubordinationProfile → Bool) : Nat :=
  (allSubProfiles.filter pred).length

/-! ## P. Per-Language Verification -/

-- Subordinator order
theorem english_initial_sub : subEnglish.subordinatorOrder == .initialWord := by native_decide
theorem japanese_final_sub : subJapanese.subordinatorOrder == .finalWord := by native_decide
theorem turkish_final_suffix : subTurkish.subordinatorOrder == .finalSuffix := by native_decide
theorem hindi_initial_sub : subHindiUrdu.subordinatorOrder == .initialWord := by native_decide
theorem korean_final_suffix : subKorean.subordinatorOrder == .finalSuffix := by native_decide
theorem quechua_final_suffix : subQuechua.subordinatorOrder == .finalSuffix := by native_decide

-- Complementizer position
theorem english_initial_comp : subEnglish.compPosition == .initial := by native_decide
theorem japanese_final_comp : subJapanese.compPosition == .final := by native_decide
theorem turkish_no_comp : subTurkish.compPosition == .none := by native_decide
theorem mandarin_no_comp : subMandarin.compPosition == .none := by native_decide

-- Relative clause position
theorem english_postnominal_rc : subEnglish.rcPosition == .postNominal := by native_decide
theorem japanese_prenominal_rc : subJapanese.rcPosition == .preNominal := by native_decide
theorem hindi_correlative_rc : subHindiUrdu.rcPosition == .correlative := by native_decide
theorem mandarin_prenominal_rc : subMandarin.rcPosition == .preNominal := by native_decide
theorem navajo_internal_rc : subNavajo.rcPosition == .internallyHeaded := by native_decide

-- OV-adposition correlation
theorem english_vo_prep : subEnglish.ovAdposition == .voPrep := by native_decide
theorem japanese_ov_postp : subJapanese.ovAdposition == .ovPostp := by native_decide
theorem persian_ov_prep : subPersian.ovAdposition == .ovPrep := by native_decide

/-! ## Q. Typological Generalizations

### Q1. Initial subordinators correlate with VO order

In our sample, every language with an initial subordinator word and VO order
shows this correlation. The disharmonic cases (OV + initial subordinator)
are Hindi-Urdu and Persian — both Iranian/Indo-Aryan languages with known
mixed headedness.
-/

/-- All VO languages in our sample have initial subordinators. -/
theorem vo_implies_initial_subordinator :
    let voLangs := allSubProfiles.filter (·.isVO)
    voLangs.all (·.hasInitialSubordinator) = true := by
  native_decide

/-- Most OV languages with final subordinators use postpositions. -/
theorem final_sub_implies_ov :
    let finalSubLangs := allSubProfiles.filter (·.hasFinalSubordinator)
    finalSubLangs.all (·.isOV) = true := by
  native_decide

/-! ### Q2. Post-nominal relative clauses are the global majority

Post-nominal RCs dominate in our sample. Pre-nominal RCs appear only
in OV languages (Japanese, Turkish, Korean, Quechua, Basque, Amharic)
plus Mandarin (which has mixed headedness).
-/

/-- Post-nominal RCs are the most common type in our sample. -/
theorem postnominal_rc_majority :
    countSubProfiles (·.hasPostNominalRC) >
    countSubProfiles (·.hasPreNominalRC) := by
  native_decide

/-- Count of post-nominal RC languages. -/
theorem postnominal_rc_count :
    countSubProfiles (·.hasPostNominalRC) = 10 := by native_decide

/-- Count of pre-nominal RC languages. -/
theorem prenominal_rc_count :
    countSubProfiles (·.hasPreNominalRC) = 7 := by native_decide

/-! ### Q3. Pre-nominal RCs strongly correlate with OV order

In our sample, all pre-nominal RC languages except Mandarin have OV order.
Mandarin is the well-known exception: SVO but pre-nominal RC, reflecting
its mixed headedness (head-initial VP, head-final NP).
-/

/-- All pre-nominal RC languages in our sample are OV, except Mandarin. -/
theorem prenominal_rc_mostly_ov :
    let preNomOV := (allSubProfiles.filter
      (λ p => p.hasPreNominalRC && p.isOV)).length
    let preNomVO := (allSubProfiles.filter
      (λ p => p.hasPreNominalRC && p.isVO)).length
    preNomOV > preNomVO * 5 := by
  native_decide

/-! ### Q4. Complementizer position mirrors subordinator position

Languages with initial subordinators tend to have initial complementizers
(or no overt complementizer). Languages with final subordinators tend to
have final complementizers (or no overt complementizer).
-/

/-- No language in our sample has initial subordinator + final complementizer. -/
theorem no_initial_sub_final_comp :
    let conflicts := allSubProfiles.filter
      (λ p => p.hasInitialSubordinator && p.compPosition == .final)
    conflicts.length = 0 := by
  native_decide

/-- No language in our sample has final subordinator + initial complementizer. -/
theorem no_final_sub_initial_comp :
    let conflicts := allSubProfiles.filter
      (λ p => p.hasFinalSubordinator && p.compPosition == .initial)
    conflicts.length = 0 := by
  native_decide

/-! ### Q5. SOV languages overwhelmingly use postpositions (Ch 95)

The OV-postposition correlation is one of the strongest in typology.
In WALS Ch 95 data, OV+Postpositions (472) dwarfs OV+Prepositions (41).
In our sample, OV languages with postpositions outnumber OV languages
with prepositions.
-/

/-- In WALS data: OV+Postpositions (472) is 11x more common than
    OV+Prepositions (41). -/
theorem ov_postpositions_dominant :
    (472 : Nat) > 41 * 11 := by native_decide

/-- In our sample, most OV languages use postpositions. -/
theorem sample_ov_mostly_postpositions :
    let ovPostp := (allSubProfiles.filter
      (λ p => p.ovAdposition == .ovPostp)).length
    let ovPrep := (allSubProfiles.filter
      (λ p => p.ovAdposition == .ovPrep)).length
    ovPostp > ovPrep * 5 := by
  native_decide

/-! ### Q6. Purpose clause strategy correlates with finiteness

Languages with productive infinitives use infinitive purpose clauses.
Languages without infinitives use subjunctive, nominalization, or serial
verb constructions. In our sample, nominalization purpose clauses appear
only in OV languages with suffixal morphology (Japanese, Turkish, Korean,
Quechua, Basque).
-/

/-- All nominalization purpose languages in our sample are OV. -/
theorem nominalization_purpose_implies_ov :
    let nomPurp := allSubProfiles.filter
      (λ p => p.purposeStrategy == .nominalization)
    nomPurp.all (·.isOV) = true := by
  native_decide

/-- Serial verb purpose clauses appear in both VO and OV languages. -/
theorem serial_verb_purpose_mixed :
    let svPurp := allSubProfiles.filter
      (λ p => p.purposeStrategy == .serialVerb)
    (svPurp.any (·.isVO)) && (svPurp.any (·.isOV)) = true := by
  native_decide

/-! ### Q7. Head-direction consistency across constructions

Languages that are consistently head-initial show initial subordinators,
initial complementizers, and post-nominal RCs. Languages that are
consistently head-final show the opposite pattern. Disharmonic languages
(Persian, Hindi-Urdu, Mandarin) are the interesting exceptions.
-/

/-- Count of "consistently head-initial" languages (initial sub + initial comp
    + post-nominal RC + VO). -/
def isConsistentlyHeadInitial (p : SubordinationProfile) : Bool :=
  p.hasInitialSubordinator && p.compPosition == .initial &&
  p.hasPostNominalRC && p.isVO

/-- Count of "consistently head-final" languages (final sub + (final comp or none)
    + pre-nominal RC + OV). -/
def isConsistentlyHeadFinal (p : SubordinationProfile) : Bool :=
  p.hasFinalSubordinator &&
  (p.compPosition == .final || p.compPosition == .none) &&
  p.hasPreNominalRC && p.isOV

/-- Most languages in our sample are consistently head-initial or head-final. -/
theorem consistency_dominant :
    let consistent := countSubProfiles isConsistentlyHeadInitial +
                      countSubProfiles isConsistentlyHeadFinal
    consistent > allSubProfiles.length / 2 := by
  native_decide

/-- Number of consistently head-initial languages (English, Arabic, Irish,
    Swahili, German, Russian, Yoruba, Tagalog, Malagasy). -/
theorem head_initial_count :
    countSubProfiles isConsistentlyHeadInitial = 9 := by native_decide

/-- Number of consistently head-final languages. -/
theorem head_final_count :
    countSubProfiles isConsistentlyHeadFinal = 6 := by native_decide

/-! ### Q8. Disharmonic languages are typologically interesting

Persian (OV + prepositions + initial comp + post-nominal RC),
Hindi-Urdu (OV + initial subordinator + correlative RC), and
Mandarin (VO + pre-nominal RC + no comp) are the three disharmonic
languages in our sample.
-/

/-- Persian is disharmonic: OV with prepositions (Ch 95 type). -/
theorem persian_disharmonic :
    subPersian.ovAdposition == .ovPrep ∧
    subPersian.compPosition == .initial ∧
    subPersian.rcPosition == .postNominal := by
  native_decide

/-- Hindi-Urdu is disharmonic: OV with initial subordinator. -/
theorem hindi_disharmonic :
    subHindiUrdu.isOV ∧ subHindiUrdu.hasInitialSubordinator := by
  native_decide

/-- Mandarin is disharmonic: VO with pre-nominal RC. -/
theorem mandarin_disharmonic :
    subMandarin.isVO ∧ subMandarin.hasPreNominalRC := by
  native_decide

/-! ### Q9. Correlative RCs are restricted to South Asian languages

In our sample, only Hindi-Urdu has correlative RCs. This is an areal
feature of South Asian languages (Hock 1989, Srivastav 1991).
-/

/-- Exactly one language in our sample has correlative RCs. -/
theorem correlative_rc_rare :
    (allSubProfiles.filter (·.rcPosition == .correlative)).length = 1 := by
  native_decide

/-- The correlative RC language is Hindi-Urdu. -/
theorem correlative_is_hindi :
    (allSubProfiles.filter (·.rcPosition == .correlative)).all
      (·.language == "Hindi-Urdu") = true := by
  native_decide

/-! ### Q10. Internally headed RCs are rare

Internally headed RCs (where the head noun appears inside the relative
clause) are typologically rare, attested in Navajo and Bambara in our
sample.
-/

/-- Exactly two languages in our sample have internally headed RCs. -/
theorem internal_rc_rare :
    (allSubProfiles.filter (·.rcPosition == .internallyHeaded)).length = 2 := by
  native_decide

/-! ### Q11. Ch 94 initial words dominate overall

Initial subordinator words (378/611 = 61.9%) are by far the most common
pattern in WALS Ch 94. Final patterns (word + suffix) together total
112/611 = 18.3%, less than one-third of the initial word count.
-/

/-- Initial subordinator words outnumber all final patterns combined. -/
theorem initial_word_dominates_final :
    (378 : Nat) > 58 + 54 := by native_decide

/-- Initial subordinator words account for over 60% of Ch 94 sample. -/
theorem initial_word_over_60_percent :
    378 * 100 > 611 * 60 := by native_decide

/-! ### Q12. Subordinator suffixes are restricted to OV languages

In WALS Ch 94, subordinator suffixes (both initial and final) are
typologically rare (7 + 54 = 61/611). In our sample, all languages
with subordinator suffixes are OV. This follows from morphological
typology: suffixal subordination requires the subordinated verb to
be identifiable by position, which OV order provides.
-/

/-- All subordinator suffix languages in our sample are OV. -/
theorem sub_suffix_implies_ov :
    let suffixLangs := allSubProfiles.filter
      (λ p => p.subordinatorOrder == .finalSuffix ||
              p.subordinatorOrder == .initialSuffix)
    suffixLangs.all (·.isOV) = true := by
  native_decide

end Phenomena.Complementation.Typology
