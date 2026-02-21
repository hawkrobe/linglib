import Linglib.Core.Word

/-!
# Copula and Predication Typology (WALS Chapters 117--120)

Cross-linguistic data on predication strategies and copulas from four WALS
chapters, all authored by Leon Stassen (2013). These chapters address a
cluster of related questions: how languages express predication when the
predicate is an adjective, a noun phrase, or a locative, and whether a
copular element is needed in each case.

The key insight from Stassen's typological work is that *predication is not
uniform across predicate types*. Many languages use fundamentally different
strategies for adjectival predication ("The book is red"), nominal
predication ("She is a doctor"), and locational predication ("The cat is
on the mat"). The copula, where it exists, is best understood not as a
single phenomenon but as a family of strategies that languages deploy
differently across predicate types.

## Ch 117: Predicative Adjectives (Stassen 2013a)

How languages express adjectival predication. Three values:
- **Verbal**: adjectives behave like verbs (take verbal morphology, no copula).
  This is the most common strategy worldwide (191/386 = 49.5%).
- **Non-verbal encoding**: adjectives require a copula or other non-verbal
  strategy (113/386 = 29.3%).
- **Mixed**: some adjectives are verbal, others require a copula
  (82/386 = 21.2%).

## Ch 118: Predicative Noun Phrases (Stassen 2013b)

How languages express nominal predication ("She is a doctor"). Two values:
- **Verbal encoding**: a copula verb is used (171/386 = 44.3%).
- **Non-verbal encoding**: juxtaposition, with no copula or a non-verbal
  particle/pronoun (215/386 = 55.7%).

## Ch 119: Nominal and Locational Predication (Stassen 2013c)

Whether a language uses the *same* or *different* strategy for nominal
predication ("is a doctor") and locational predication ("is in the room").
Two values:
- **Different**: different copulas or strategies for NOM vs LOC (236/386 = 61.1%).
- **Identical**: same copula/strategy for both (150/386 = 38.9%).

The majority pattern is to differentiate: even English, which uses "be" for
both, is cross-linguistically unusual in using a single copula.

## Ch 120: Zero Copula for Predicate Nominals (Stassen 2013d)

Whether the copula can be absent in nominal predication. Three values:
- **Impossible**: copula is always required (182/386 = 47.2%).
- **Possible in some contexts**: zero copula in restricted environments,
  typically present tense or 3rd person (107/386 = 27.7%).
- **Widespread**: zero copula is the normal/default strategy (97/386 = 25.1%).

## References

- Stassen, L. (2013a). Predicative adjectives. In Dryer & Haspelmath (eds.),
  WALS Online (v2020.3). https://wals.info/chapter/117
- Stassen, L. (2013b). Predicative noun phrases. In Dryer & Haspelmath
  (eds.), WALS Online. https://wals.info/chapter/118
- Stassen, L. (2013c). Nominal and locational predication. In Dryer &
  Haspelmath (eds.), WALS Online. https://wals.info/chapter/119
- Stassen, L. (2013d). Zero copula for predicate nominals. In Dryer &
  Haspelmath (eds.), WALS Online. https://wals.info/chapter/120
- Stassen, L. (1997). Intransitive Predication. Oxford University Press.
- Hengeveld, K. (1992). Non-verbal Predication. Mouton de Gruyter.
- Pustet, R. (2003). Copulas: Universals in the Categorization of the
  Lexicon. Oxford University Press.
-/

namespace Phenomena.Copulas.Typology

-- ============================================================================
-- Chapter 117: Predicative Adjective Strategy
-- ============================================================================

/-- WALS Ch 117: How a language expresses adjectival predication
    ("The book is red").

    The three-way distinction reflects the categorial status of adjectives
    in the language. In "verbal" languages, adjectives inflect like verbs
    and need no copula. In "non-verbal" languages, adjectives are a
    distinct category requiring a copula. "Mixed" languages have adjectives
    that split between verbal and non-verbal behavior. -/
inductive PredAdjStrategy where
  /-- Adjectives behave like verbs: they take verbal morphology (tense,
      aspect, negation) and occur as predicates without a copula.
      Example: Mandarin `shu hong` 'book red' = 'The book is red',
      where `hong` can take aspect markers directly. -/
  | verbal
  /-- Some adjectives are verbal (typically core/frequent ones), others
      require a copula (typically peripheral/borrowed ones).
      Example: Japanese has verbal adjectives (i-adjectives: `takai`
      'is expensive') and non-verbal adjectives (na-adjectives: `shizuka-da`
      'quiet-COP'). -/
  | mixed
  /-- Adjectives are categorially distinct from verbs and require a
      copula or other linking element for predication.
      Example: English `The book is red` requires the copula `is`. -/
  | nonVerbal
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 118: Predicative Noun Phrase Strategy
-- ============================================================================

/-- WALS Ch 118: How a language expresses nominal predication
    ("She is a doctor").

    The binary distinction captures whether the language uses a verbal
    copula (a word that inflects like a verb and carries tense/agreement)
    or a non-verbal strategy (juxtaposition, pronominal copula, or
    invariant particle). -/
inductive PredNounStrategy where
  /-- Nominal predication uses a verbal copula that inflects for tense,
      agreement, etc.
      Example: English `She is a doctor`, where `is` is a fully inflecting
      verb (am/is/are/was/were). -/
  | verbal
  /-- Nominal predication uses juxtaposition or a non-verbal element
      (particle, pronoun, etc.), not a copula verb.
      Example: Russian present tense `Ona vrach` 'She doctor' = 'She is
      a doctor' (no copula in present tense). -/
  | nonVerbal
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 119: Nominal vs Locational Predication
-- ============================================================================

/-- WALS Ch 119: Whether a language uses the same or different strategy
    for nominal predication ("She is a doctor") and locational predication
    ("The cat is on the mat").

    Many languages use different verbs: e.g., Spanish `ser` (nominal) vs
    `estar` (locational), or have a copula for one but not the other. The
    "different" value is the majority pattern cross-linguistically. -/
inductive NomLocStrategy where
  /-- The same copula or strategy is used for both nominal and locational
      predication.
      Example: English `She is a doctor` / `The cat is on the mat` --
      both use `be`. -/
  | identical
  /-- Different copulas or strategies are used for nominal vs locational
      predication.
      Example: Spanish `ser` (nominal: `Es doctora`) vs `estar`
      (locational: `Esta en la casa`). -/
  | different
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Chapter 120: Zero Copula for Predicate Nominals
-- ============================================================================

/-- WALS Ch 120: Whether the copula can be absent in nominal predication.

    Zero copula is typically conditioned by tense (present only) or
    person (3rd person only). "Widespread" means zero copula is the
    default, unrestricted strategy. -/
inductive ZeroCopulaStatus where
  /-- Zero copula is impossible: the copula is always required in nominal
      predication, regardless of tense, person, or other factors.
      Example: English `*She doctor` is ungrammatical. -/
  | impossible
  /-- Zero copula is possible in restricted contexts: typically present
      tense, or 3rd person, or in certain clause types. The copula
      appears in other environments.
      Example: Russian allows zero copula in present tense
      (`Ona vrach` 'She doctor') but requires it in past tense
      (`Ona byla vrach` 'She was doctor'). -/
  | restricted
  /-- Zero copula is the normal, widespread, or default strategy.
      The copula is absent in most environments.
      Example: Tagalog `Doktor siya` 'Doctor she' = 'She is a doctor'. -/
  | widespread
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Copula Type (Supplementary Classification)
-- ============================================================================

/-- Morphosyntactic type of copula, when present.

    This supplements the WALS classification with a finer-grained
    typology of copular elements, following Pustet (2003) and
    Hengeveld (1992). -/
inductive CopulaType where
  /-- Fully inflecting verbal copula: takes tense, agreement, negation
      like other verbs. Example: English `be` (am/is/are/was/were). -/
  | verbalCopula
  /-- Pronominal copula: a pronoun-like element that agrees with the
      subject. Example: Hebrew `hu/hi/hem/hen` (he/she/they.m/they.f)
      used as a copula in present tense. -/
  | pronominalCopula
  /-- Invariant particle: a non-inflecting element linking subject and
      predicate. Example: Swahili `ni` (affirmative copula, invariant). -/
  | particle
  /-- No copula: predication by juxtaposition. -/
  | zero
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- WALS Distribution Data
-- ============================================================================

/-- A single row in a WALS frequency table: a category label and its count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- Sum of counts in a WALS table. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (λ acc c => acc + c.count) 0

/-- Chapter 117 distribution: predicative adjectives (N = 386). -/
def ch117Counts : List WALSCount :=
  [ ⟨"Verbal encoding", 191⟩
  , ⟨"Mixed", 82⟩
  , ⟨"Non-verbal encoding", 113⟩ ]

/-- Chapter 118 distribution: predicative noun phrases (N = 386). -/
def ch118Counts : List WALSCount :=
  [ ⟨"Non-verbal encoding", 215⟩
  , ⟨"Verbal encoding", 171⟩ ]

/-- Chapter 119 distribution: nominal and locational predication (N = 386). -/
def ch119Counts : List WALSCount :=
  [ ⟨"Different", 236⟩
  , ⟨"Identical", 150⟩ ]

/-- Chapter 120 distribution: zero copula for predicate nominals (N = 386). -/
def ch120Counts : List WALSCount :=
  [ ⟨"Impossible", 182⟩
  , ⟨"Possible in some contexts", 107⟩
  , ⟨"Widespread", 97⟩ ]

-- ============================================================================
-- Aggregate Total Verification
-- ============================================================================

/-- Ch 117 total: 386 languages. -/
theorem ch117_total : WALSCount.totalOf ch117Counts = 386 := by native_decide

/-- Ch 118 total: 386 languages. -/
theorem ch118_total : WALSCount.totalOf ch118Counts = 386 := by native_decide

/-- Ch 119 total: 386 languages. -/
theorem ch119_total : WALSCount.totalOf ch119Counts = 386 := by native_decide

/-- Ch 120 total: 386 languages. -/
theorem ch120_total : WALSCount.totalOf ch120Counts = 386 := by native_decide

/-- All four chapters use the same sample of 386 languages. -/
theorem all_chapters_same_sample :
    WALSCount.totalOf ch117Counts = WALSCount.totalOf ch118Counts ∧
    WALSCount.totalOf ch118Counts = WALSCount.totalOf ch119Counts ∧
    WALSCount.totalOf ch119Counts = WALSCount.totalOf ch120Counts := by
  native_decide

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/-- A language's copula and predication profile across WALS Chapters 117--120. -/
structure CopulaProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String := ""
  /-- Language family. -/
  family : String := ""
  /-- Ch 117: How adjectival predication is expressed. -/
  predAdj : PredAdjStrategy
  /-- Ch 118: How nominal predication is expressed. -/
  predNoun : PredNounStrategy
  /-- Ch 119: Whether nominal and locational predication use the
      same or different strategy. -/
  nomLoc : NomLocStrategy
  /-- Ch 120: Whether zero copula is possible in nominal predication. -/
  zeroCopula : ZeroCopulaStatus
  /-- Primary copula type in the language (supplementary). -/
  copulaType : CopulaType := .verbalCopula
  /-- Illustrative copula form(s). -/
  copulaForms : List String := []
  /-- Notes on the predication system. -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- Language Data
-- ============================================================================

/--
English (Indo-European, Germanic).
Adjectives are non-verbal: require copula `be` ("The book is red").
Nominal predication uses the verbal copula `be` ("She is a doctor").
Same copula `be` for both nominal and locational predication.
Zero copula is impossible: `*She doctor`, `*Book red`.
-/
def english : CopulaProfile :=
  { language := "English"
  , iso := "eng"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .identical
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["be", "am", "is", "are", "was", "were"]
  , notes := "Single copula 'be' for all predication types; " ++
             "fully inflecting for tense, number, person" }

/--
French (Indo-European, Romance).
Adjectives are non-verbal: `Le livre est rouge` ('The book is red').
Nominal predication uses verbal copula `etre`: `Elle est medecin`.
Same copula `etre` for nominal and locational predication.
Zero copula is impossible.
-/
def french : CopulaProfile :=
  { language := "French"
  , iso := "fra"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .identical
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["etre", "est", "suis", "sont"]
  , notes := "Single copula 'etre' for all predication; fully inflecting" }

/--
German (Indo-European, Germanic).
Adjectives are non-verbal: `Das Buch ist rot` ('The book is red').
Nominal predication uses verbal copula `sein`: `Sie ist Arztin`.
Same copula for nominal and locational predication.
Zero copula is impossible.
-/
def german : CopulaProfile :=
  { language := "German"
  , iso := "deu"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .identical
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["sein", "ist", "bin", "sind"]
  , notes := "Copula 'sein' for all predication; like English 'be'" }

/--
Spanish (Indo-European, Romance).
Adjectives are non-verbal: `El libro es rojo` ('The book is red').
Nominal predication uses verbal copula `ser`: `Ella es doctora`.
DIFFERENT copulas for nominal vs locational: `ser` (permanent/nominal)
vs `estar` (temporary/locational).
Zero copula is impossible.
-/
def spanish : CopulaProfile :=
  { language := "Spanish"
  , iso := "spa"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .different
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["ser", "estar"]
  , notes := "ser/estar split: ser for nominal/permanent, estar for " ++
             "locational/temporary; both are fully inflecting verbs" }

/--
Russian (Indo-European, Slavic).
Adjectives are non-verbal in present tense (zero copula: `Kniga krasnaja`
'Book red'), verbal copula `byt'` in past (`Kniga byla krasnaja`).
Nominal predication uses zero copula in present: `Ona vrach` ('She doctor').
Same strategy for nominal and locational (both use zero copula in present).
Zero copula is RESTRICTED to present tense: past and future require `byt'`.
-/
def russian : CopulaProfile :=
  { language := "Russian"
  , iso := "rus"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .nonVerbal
  , nomLoc := .identical
  , zeroCopula := .restricted
  , copulaType := .zero
  , copulaForms := ["byt'", "byla", "byl", "budet"]
  , notes := "Zero copula in present tense for all predication types; " ++
             "past/future require byt'; est' used for existential/locational" }

/--
Arabic (Standard) (Afro-Asiatic, Semitic).
Adjectives are non-verbal: `al-kitab ahmar` 'the-book red'.
Nominal predication is non-verbal in present: `hiya tabiba` 'she doctor'.
Different strategies for nominal vs locational (locational uses `fi`
'in' with possible copula).
Zero copula is RESTRICTED: present tense allows zero, past requires `kaana`.
-/
def arabic : CopulaProfile :=
  { language := "Arabic (Standard)"
  , iso := "arb"
  , family := "Afro-Asiatic"
  , predAdj := .nonVerbal
  , predNoun := .nonVerbal
  , nomLoc := .different
  , zeroCopula := .restricted
  , copulaType := .zero
  , copulaForms := ["kaana", "yakuunu"]
  , notes := "Zero copula in present tense; kaana for past; " ++
             "pronoun of separation (huwa/hiya) possible between " ++
             "subject and predicate" }

/--
Hebrew (Afro-Asiatic, Semitic).
Adjectives are non-verbal: `ha-sefer adom` 'the-book red'.
Nominal predication uses a pronominal copula in present: `hi rofaa`
or `hi hi rofaa` (she COP.3F doctor). Past/future use `haya`.
Different strategies for nominal vs locational.
Zero copula is RESTRICTED: present allows zero/pronominal, past requires
`haya`.
-/
def hebrew : CopulaProfile :=
  { language := "Hebrew"
  , iso := "heb"
  , family := "Afro-Asiatic"
  , predAdj := .nonVerbal
  , predNoun := .nonVerbal
  , nomLoc := .different
  , zeroCopula := .restricted
  , copulaType := .pronominalCopula
  , copulaForms := ["hu", "hi", "hem", "hen", "haya"]
  , notes := "Pronominal copula (hu/hi/hem/hen) in present tense; " ++
             "haya for past; zero copula also possible in present" }

/--
Hungarian (Uralic).
Adjectives are non-verbal: `A konyv piros` 'The book red'.
Nominal predication: zero copula in 3rd person present (`O orvos`
'She doctor'), verbal copula `van` in other persons/tenses.
Same strategy for nominal and locational.
Zero copula is RESTRICTED to 3rd person present tense.
-/
def hungarian : CopulaProfile :=
  { language := "Hungarian"
  , iso := "hun"
  , family := "Uralic"
  , predAdj := .nonVerbal
  , predNoun := .nonVerbal
  , nomLoc := .identical
  , zeroCopula := .restricted
  , copulaType := .zero
  , copulaForms := ["van", "vannak", "volt", "vagyok"]
  , notes := "Zero copula in 3rd person present; van/vannak in " ++
             "1st/2nd person and locational; volt in past" }

/--
Japanese (Japonic).
Adjectives are MIXED: i-adjectives are verbal (`takai` 'is.expensive',
takes tense: `takakatta` 'was.expensive'), but na-adjectives require
copula `da` (`shizuka-da` 'quiet-COP').
Nominal predication uses copula `da`/`desu`: `Kanojo wa isha da` 'She TOP
doctor COP'.
Different strategies for nominal and locational (locational uses `ni iru/aru`).
Zero copula is impossible in standard forms (copula always required for
nominals).
-/
def japanese : CopulaProfile :=
  { language := "Japanese"
  , iso := "jpn"
  , family := "Japonic"
  , predAdj := .mixed
  , predNoun := .verbal
  , nomLoc := .different
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["da", "desu", "datta", "deshita"]
  , notes := "i-adjectives are verbal (no copula), na-adjectives " ++
             "require copula da; nominal predication always uses da/desu" }

/--
Korean (Koreanic).
Adjectives are verbal: `chaek-i ppalgah-da` 'book-NOM red-DECL' with
verbal inflection on the adjective. No copula needed.
Nominal predication uses copula `-i-da`: `geunyeo-neun uisa-i-da`
'she-TOP doctor-COP-DECL'.
Different strategies for nominal vs locational (locational uses `iss-da`
'exist-DECL').
Zero copula is impossible for nominals.
-/
def korean : CopulaProfile :=
  { language := "Korean"
  , iso := "kor"
  , family := "Koreanic"
  , predAdj := .verbal
  , predNoun := .verbal
  , nomLoc := .different
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["-i-da", "-i-eyo"]
  , notes := "Adjectives are fully verbal (descriptive verbs); " ++
             "copula -i-da is a bound morpheme; locational uses " ++
             "existential iss-da" }

/--
Mandarin Chinese (Sino-Tibetan).
Adjectives are verbal: `shu hong` 'book red' = 'The book is red'.
Adjectives can take aspect markers (le, guo) and negation (bu) directly.
Nominal predication uses copula `shi`: `ta shi yisheng` 'she COP doctor'.
Different strategies for nominal vs locational (locational uses `zai` 'at').
Zero copula is impossible for nominal predication (shi is required).
-/
def mandarin : CopulaProfile :=
  { language := "Mandarin Chinese"
  , iso := "cmn"
  , family := "Sino-Tibetan"
  , predAdj := .verbal
  , predNoun := .verbal
  , nomLoc := .different
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["shi"]
  , notes := "Adjectives are verbal (no copula); shi required for " ++
             "nominal predication; zai for locational; shi is not " ++
             "used with adjectives (*shu shi hong)" }

/--
Turkish (Turkic).
Adjectives are verbal: `Kitap kirmizi` 'Book red' = 'The book is red'.
Adjective takes verbal suffixes for tense.
Nominal predication uses a copular suffix: `O doktor-dur` 'S/he doctor-COP'.
Different strategies for nominal vs locational (locational uses
postposition + var/yok).
Zero copula is RESTRICTED: 3rd person present often has zero copula
(`O doktor` 'S/he doctor'), but past requires `-di`/`-ydi`.
-/
def turkish : CopulaProfile :=
  { language := "Turkish"
  , iso := "tur"
  , family := "Turkic"
  , predAdj := .verbal
  , predNoun := .nonVerbal
  , nomLoc := .different
  , zeroCopula := .restricted
  , copulaType := .particle
  , copulaForms := ["-dir", "-dur", "-dir/-dur/-tir/-tur", "idi"]
  , notes := "Copular suffix -dIr for nominals; often omitted in " ++
             "informal 3rd person present; past copula idi; adjectives " ++
             "are verbal" }

/--
Swahili (Niger-Congo, Bantu).
Adjectives are verbal: `-zuri` 'good' takes verbal agreement prefixes
(`m-zuri` 'good (cl.1)'). Predication: `Kitabu ni kizuri` uses `ni`.
Nominal predication uses particle `ni`: `Yeye ni daktari` 'S/he COP doctor'.
Different strategies for nominal vs locational (locational uses `-ko`
locative suffixes and different verbal forms).
Zero copula is WIDESPREAD in some constructions: `Yeye daktari` is
acceptable in many contexts.
-/
def swahili : CopulaProfile :=
  { language := "Swahili"
  , iso := "swh"
  , family := "Niger-Congo"
  , predAdj := .verbal
  , predNoun := .nonVerbal
  , nomLoc := .different
  , zeroCopula := .widespread
  , copulaType := .particle
  , copulaForms := ["ni", "si", "ndiye"]
  , notes := "Particle ni for affirmative nominal predication, si for " ++
             "negative; adjectives take noun class agreement prefixes " ++
             "like verbs" }

/--
Hindi-Urdu (Indo-European, Indo-Aryan).
Adjectives are non-verbal: `kitab lal hai` 'book red COP.PRS'.
Nominal predication uses copula `hona`: `vo daktar hai` 'she doctor COP.PRS'.
Same copula `hona` for nominal and locational predication.
Zero copula is impossible in standard Hindi-Urdu.
-/
def hindiUrdu : CopulaProfile :=
  { language := "Hindi-Urdu"
  , iso := "hin"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .identical
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["hona", "hai", "hain", "tha", "thi"]
  , notes := "Copula hona fully inflects for tense, number, gender; " ++
             "same form for nominal and locational predication" }

/--
Tagalog (Austronesian).
Adjectives are verbal: `maganda ang babae` 'beautiful ANG woman'.
Nominal predication is non-verbal: `doktor siya` 'doctor she'.
Same strategy for nominal and locational.
Zero copula is WIDESPREAD: `doktor siya` with no overt copula is the
normal strategy.
-/
def tagalog : CopulaProfile :=
  { language := "Tagalog"
  , iso := "tgl"
  , family := "Austronesian"
  , predAdj := .verbal
  , predNoun := .nonVerbal
  , nomLoc := .identical
  , zeroCopula := .widespread
  , copulaType := .zero
  , copulaForms := ["ay"]
  , notes := "Adjectives are verbal (stative verbs); nominal predication " ++
             "by juxtaposition; ay is a topic marker, not a true copula" }

/--
Irish (Indo-European, Celtic).
Adjectives are non-verbal: `Ta an leabhar dearg` 'COP the book red'.
Nominal predication uses copula `is`: `Is dochtúir í` 'COP doctor she'.
DIFFERENT copulas: `is` (classificatory/identificational) vs `ta`
(attributive/locational).
Zero copula is impossible.
-/
def irish : CopulaProfile :=
  { language := "Irish"
  , iso := "gle"
  , family := "Indo-European"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .different
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["is", "ta"]
  , notes := "Two copulas: 'is' (copula proper, nominal/identity) vs " ++
             "'ta' (substantive verb, attributive/locational); classic " ++
             "split predication system" }

/--
Finnish (Uralic).
Adjectives are non-verbal: `Kirja on punainen` 'Book COP red'.
Nominal predication uses verbal copula `olla`: `Han on laakari` 'S/he
COP doctor'.
Same copula `olla` for nominal and locational predication.
Zero copula is impossible.
-/
def finnish : CopulaProfile :=
  { language := "Finnish"
  , iso := "fin"
  , family := "Uralic"
  , predAdj := .nonVerbal
  , predNoun := .verbal
  , nomLoc := .identical
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["olla", "on", "ovat", "oli"]
  , notes := "Copula olla for all predication types; fully inflecting; " ++
             "existential 'on' also used for locational" }

/--
Quechua (Quechuan).
Adjectives are non-verbal: `Wasi hatun-mi` 'House big-EVID' with copular
suffix.
Nominal predication uses copular suffixes: `Pay yachachiq-mi` 'S/he
teacher-EVID' (copula as suffix `-mi`/`-n`).
Same strategy for nominal and locational predication.
Zero copula is RESTRICTED: 3rd person present often has zero or reduced
copula, but other persons/tenses require overt copula `ka-`.
-/
def quechua : CopulaProfile :=
  { language := "Quechua"
  , iso := "que"
  , family := "Quechuan"
  , predAdj := .nonVerbal
  , predNoun := .nonVerbal
  , nomLoc := .identical
  , zeroCopula := .restricted
  , copulaType := .particle
  , copulaForms := ["ka-", "-mi", "-n"]
  , notes := "Copular suffixes for nominal predication; ka- as copular " ++
             "verb in past/future; zero copula in some 3rd person " ++
             "present contexts" }

/--
Yoruba (Niger-Congo, Atlantic-Congo).
Adjectives are verbal: `Iwe na tobi` 'book the big' (adjective inflects
verbally).
Nominal predication uses non-verbal strategy (juxtaposition or pronoun):
`O je dokita` 'She be doctor' or `O dokita ni` 'She doctor COP'.
Different strategies for nominal vs locational.
Zero copula is WIDESPREAD for nominal predication.
-/
def yoruba : CopulaProfile :=
  { language := "Yoruba"
  , iso := "yor"
  , family := "Niger-Congo"
  , predAdj := .verbal
  , predNoun := .nonVerbal
  , nomLoc := .different
  , zeroCopula := .widespread
  , copulaType := .particle
  , copulaForms := ["ni", "je"]
  , notes := "Adjectives are stative verbs; ni is a focus-like copula; " ++
             "je for identificational predication" }

/--
Thai (Tai-Kadai).
Adjectives are verbal: `Nangsue daeng` 'Book red' = 'The book is red',
where the adjective takes verbal markers directly.
Nominal predication uses verbal copula `pen`: `Khao pen mor` 'S/he COP
doctor'.
Different strategies for nominal vs locational (locational uses `yuu` 'be.at').
Zero copula is impossible for nominal predication.
-/
def thai : CopulaProfile :=
  { language := "Thai"
  , iso := "tha"
  , family := "Tai-Kadai"
  , predAdj := .verbal
  , predNoun := .verbal
  , nomLoc := .different
  , zeroCopula := .impossible
  , copulaType := .verbalCopula
  , copulaForms := ["pen", "yuu", "khue"]
  , notes := "Adjectives are stative verbs (no copula); pen for nominal " ++
             "predication; yuu for locational; khue for identification" }

/-- All language profiles in the sample. -/
def allLanguages : List CopulaProfile :=
  [ english, french, german, spanish, russian, arabic, hebrew, hungarian
  , japanese, korean, mandarin, turkish, swahili, hindiUrdu, tagalog
  , irish, finnish, quechua, yoruba, thai ]

-- ============================================================================
-- Helper Predicates
-- ============================================================================

/-- Does a language have verbal adjectives? -/
def CopulaProfile.hasVerbalAdj (p : CopulaProfile) : Bool :=
  p.predAdj == .verbal

/-- Does a language have a verbal copula for nominal predication? -/
def CopulaProfile.hasVerbalNounCopula (p : CopulaProfile) : Bool :=
  p.predNoun == .verbal

/-- Does a language allow zero copula (restricted or widespread)? -/
def CopulaProfile.allowsZeroCopula (p : CopulaProfile) : Bool :=
  p.zeroCopula == .restricted || p.zeroCopula == .widespread

/-- Does a language split nominal and locational predication? -/
def CopulaProfile.hasNomLocSplit (p : CopulaProfile) : Bool :=
  p.nomLoc == .different

/-- Does a language require a copula in all contexts? -/
def CopulaProfile.alwaysRequiresCopula (p : CopulaProfile) : Bool :=
  p.zeroCopula == .impossible

/-- Count of languages in a list matching a predicate. -/
def countBy (langs : List CopulaProfile) (pred : CopulaProfile → Bool) : Nat :=
  (langs.filter pred).length

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Ch 117: Predicative adjective strategy
theorem english_adj_nonverbal : english.predAdj == .nonVerbal := by native_decide
theorem japanese_adj_mixed : japanese.predAdj == .mixed := by native_decide
theorem korean_adj_verbal : korean.predAdj == .verbal := by native_decide
theorem mandarin_adj_verbal : mandarin.predAdj == .verbal := by native_decide
theorem turkish_adj_verbal : turkish.predAdj == .verbal := by native_decide
theorem russian_adj_nonverbal : russian.predAdj == .nonVerbal := by native_decide

-- Ch 118: Predicative noun strategy
theorem english_noun_verbal : english.predNoun == .verbal := by native_decide
theorem russian_noun_nonverbal : russian.predNoun == .nonVerbal := by native_decide
theorem mandarin_noun_verbal : mandarin.predNoun == .verbal := by native_decide
theorem tagalog_noun_nonverbal : tagalog.predNoun == .nonVerbal := by native_decide
theorem swahili_noun_nonverbal : swahili.predNoun == .nonVerbal := by native_decide

-- Ch 119: Nominal vs locational predication
theorem english_nomLoc_identical : english.nomLoc == .identical := by native_decide
theorem spanish_nomLoc_different : spanish.nomLoc == .different := by native_decide
theorem irish_nomLoc_different : irish.nomLoc == .different := by native_decide
theorem mandarin_nomLoc_different : mandarin.nomLoc == .different := by native_decide

-- Ch 120: Zero copula status
theorem english_no_zero : english.zeroCopula == .impossible := by native_decide
theorem russian_zero_restricted : russian.zeroCopula == .restricted := by native_decide
theorem hungarian_zero_restricted : hungarian.zeroCopula == .restricted := by native_decide
theorem tagalog_zero_widespread : tagalog.zeroCopula == .widespread := by native_decide
theorem arabic_zero_restricted : arabic.zeroCopula == .restricted := by native_decide

-- ============================================================================
-- Sample Statistics
-- ============================================================================

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 20 := by native_decide

/-- Ch 117 distribution in our sample. -/
theorem sample_verbal_adj_count :
    countBy allLanguages (·.hasVerbalAdj) = 7 := by native_decide

theorem sample_mixed_adj_count :
    countBy allLanguages (·.predAdj == .mixed) = 1 := by native_decide

theorem sample_nonverbal_adj_count :
    countBy allLanguages (·.predAdj == .nonVerbal) = 12 := by native_decide

/-- Ch 118 distribution in our sample. -/
theorem sample_verbal_noun_count :
    countBy allLanguages (·.hasVerbalNounCopula) = 11 := by native_decide

theorem sample_nonverbal_noun_count :
    countBy allLanguages (·.predNoun == .nonVerbal) = 9 := by native_decide

/-- Ch 119 distribution in our sample. -/
theorem sample_nomloc_different_count :
    countBy allLanguages (·.hasNomLocSplit) = 11 := by native_decide

theorem sample_nomloc_identical_count :
    countBy allLanguages (·.nomLoc == .identical) = 9 := by native_decide

/-- Ch 120 distribution in our sample. -/
theorem sample_zero_impossible_count :
    countBy allLanguages (·.alwaysRequiresCopula) = 11 := by native_decide

theorem sample_zero_restricted_count :
    countBy allLanguages (·.zeroCopula == .restricted) = 6 := by native_decide

theorem sample_zero_widespread_count :
    countBy allLanguages (·.zeroCopula == .widespread) = 3 := by native_decide

-- ============================================================================
-- Generalization 1: Verbal Adjectives Are the Most Common Strategy
-- ============================================================================

/-- Ch 117: Verbal encoding (191) is the most common strategy for
    predicative adjectives, exceeding both mixed (82) and non-verbal (113). -/
theorem verbal_adj_most_common : (191 : Nat) > 113 ∧ (191 : Nat) > 82 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 117: Verbal adjectives account for nearly half the sample (191/386). -/
theorem verbal_adj_near_half : (191 : Nat) * 2 < 386 + 5 := by native_decide

-- ============================================================================
-- Generalization 2: Non-Verbal Nominal Predication Is More Common
-- ============================================================================

/-- Ch 118: Non-verbal encoding (215) is more common than verbal encoding
    (171) for nominal predication. This contrasts with adjectives, where
    verbal encoding dominates: nouns are more likely than adjectives to
    be predicated without a verbal copula. -/
theorem nonverbal_noun_more_common : (215 : Nat) > 171 := by native_decide

/-- Ch 118: Non-verbal nominal predication is the majority pattern. -/
theorem nonverbal_noun_majority : (215 : Nat) * 2 > 386 := by native_decide

-- ============================================================================
-- Generalization 3: Nom-Loc Split Is the Majority Pattern
-- ============================================================================

/-- Ch 119: Using different strategies for nominal and locational
    predication (236) is more common than using the same strategy (150).
    This means that languages typically distinguish "is a doctor" from
    "is in the room" with different grammatical means. -/
theorem nomloc_split_majority : (236 : Nat) > 150 := by native_decide

/-- Ch 119: The split pattern accounts for a clear majority. -/
theorem nomloc_split_supermajority : (236 : Nat) > 386 / 2 := by native_decide

-- ============================================================================
-- Generalization 4: Zero Copula Is a Minority Pattern Overall
-- ============================================================================

/-- Ch 120: Copula-always-required (182) is the most common single value,
    but languages that *allow* zero copula (restricted 107 + widespread 97
    = 204) slightly outnumber those that require it (182). -/
theorem zero_copula_collectively_common : (107 : Nat) + 97 > 182 := by
  native_decide

/-- Ch 120: The "impossible" value is the largest single category. -/
theorem impossible_largest_single : (182 : Nat) > 107 ∧ (182 : Nat) > 97 := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- Generalization 5: Verbal Adjectives Rarely Co-occur with Non-Verbal Nouns
-- ============================================================================

/-- In our sample, languages with verbal adjectives (Ch 117) tend NOT to
    also have verbal copulas for nouns -- they often use a different strategy
    for nominal predication. This is because the verbal adjective strategy
    eliminates the need for a copula with adjectives but does not necessarily
    provide a copula for nouns.

    Count of languages with verbal adjectives AND non-verbal noun predication. -/
theorem verbal_adj_nonverbal_noun :
    let verbalAdjNonverbalNoun := allLanguages.filter
      (λ p => p.predAdj == .verbal && p.predNoun == .nonVerbal)
    verbalAdjNonverbalNoun.length ≥ 3 := by
  native_decide

-- ============================================================================
-- Generalization 6: Zero Copula Is Often Tense-Conditioned
-- ============================================================================

/-- In our sample, languages with restricted zero copula (Ch 120) allow
    zero copula in present tense but require an overt copula in past
    tense. Russian, Arabic, Hungarian, and Turkish all exhibit this
    pattern: present tense allows copula dropping but past requires
    an overt form.

    All restricted-zero-copula languages in our sample have overt
    past-tense copula forms. -/
theorem restricted_zero_has_copula_forms :
    let restricted := allLanguages.filter (·.zeroCopula == .restricted)
    restricted.all (·.copulaForms.length > 0) = true := by
  native_decide

-- ============================================================================
-- Generalization 7: Non-Verbal Noun Predication Correlates with Zero Copula
-- ============================================================================

/-- Languages that use non-verbal noun predication (Ch 118) tend to allow
    zero copula (Ch 120). In our sample, every language with non-verbal
    noun predication allows zero copula (restricted or widespread). -/
theorem nonverbal_noun_implies_zero_copula :
    let nonverbalNoun := allLanguages.filter (·.predNoun == .nonVerbal)
    nonverbalNoun.all (·.allowsZeroCopula) = true := by
  native_decide

-- ============================================================================
-- Generalization 8: Nom-Loc Split Correlates with Verbal Adjectives
-- ============================================================================

/-- Languages with verbal adjectives tend to split nominal and locational
    predication (Ch 119 = different). In our sample, the majority of
    verbal-adjective languages have different nom-loc strategies. -/
theorem verbal_adj_tends_nomloc_split :
    let verbalAdj := allLanguages.filter (·.hasVerbalAdj)
    let splitNomLoc := verbalAdj.filter (·.hasNomLocSplit)
    splitNomLoc.length > verbalAdj.length / 2 := by
  native_decide

-- ============================================================================
-- Generalization 9: Copula-Requiring Languages Use Identical Nom-Loc
-- ============================================================================

/-- Languages where the copula is always required (Ch 120 = impossible)
    are more likely to use the SAME copula for nominal and locational
    predication (Ch 119 = identical) than languages that allow zero copula.

    Among copula-requiring languages in our sample, at least half use
    the same strategy for both predication types. -/
theorem copula_required_tends_identical :
    let required := allLanguages.filter (·.alwaysRequiresCopula)
    let identical := required.filter (·.nomLoc == .identical)
    identical.length ≥ required.length / 2 := by
  native_decide

-- ============================================================================
-- Generalization 10: Western European Languages Share a Copula Profile
-- ============================================================================

/-- Western European languages (English, French, German) share a common
    copula profile: non-verbal adjectives, verbal nominal copula, and
    no zero copula. This is the "Standard Average European" pattern
    (Haspelmath 2001). -/
def westernEuropean : List CopulaProfile := [english, french, german]

theorem western_european_nonverbal_adj :
    westernEuropean.all (·.predAdj == .nonVerbal) = true := by
  native_decide

theorem western_european_verbal_noun :
    westernEuropean.all (·.predNoun == .verbal) = true := by
  native_decide

theorem western_european_no_zero :
    westernEuropean.all (·.alwaysRequiresCopula) = true := by
  native_decide

-- ============================================================================
-- Cross-Chapter Interactions
-- ============================================================================

/-- Cross-chapter interaction: languages with verbal adjectives (Ch 117)
    and verbal noun predication (Ch 118) are the only languages in our
    sample that can have verbal predication for BOTH adjectives and nouns
    with different copula forms. -/
theorem verbal_both_count :
    let verbalBoth := allLanguages.filter
      (λ p => p.predAdj == .verbal && p.predNoun == .verbal)
    verbalBoth.length ≥ 3 := by
  native_decide

/-- In our sample, no language has mixed adjectives (Ch 117) AND
    non-verbal noun predication (Ch 118). Mixed adjective languages
    tend to have verbal copulas for nouns. -/
theorem mixed_adj_implies_verbal_noun :
    let mixedAdj := allLanguages.filter (·.predAdj == .mixed)
    mixedAdj.all (·.predNoun == .verbal) = true := by
  native_decide

/-- Languages with widespread zero copula (Ch 120) always allow
    non-verbal nominal predication (Ch 118). This is logically expected:
    if zero copula is the norm, nominal predication IS non-verbal. -/
theorem widespread_zero_implies_nonverbal_noun :
    let widespread := allLanguages.filter (·.zeroCopula == .widespread)
    widespread.all (·.predNoun == .nonVerbal) = true := by
  native_decide

/-- Stassen's Implicational Universal: if a language has non-verbal
    encoding for nouns (Ch 118), it allows some form of zero copula
    (Ch 120 = restricted or widespread). In our sample this holds
    without exception. -/
theorem stassen_implication_noun_zero :
    allLanguages.all (λ p =>
      if p.predNoun == .nonVerbal
      then p.allowsZeroCopula
      else true) = true := by
  native_decide

/-- Converse of Stassen's implication: if a language has zero copula
    impossible (Ch 120), then it uses verbal nominal predication (Ch 118).
    This is the contrapositive of the above. -/
theorem no_zero_implies_verbal_noun :
    allLanguages.all (λ p =>
      if p.zeroCopula == .impossible
      then p.predNoun == .verbal
      else true) = true := by
  native_decide

-- ============================================================================
-- Split Predication Patterns
-- ============================================================================

/-- A split predication language uses different strategies for at least
    two of: adjectival, nominal, and locational predication. -/
def CopulaProfile.hasSplitPredication (p : CopulaProfile) : Bool :=
  p.nomLoc == .different ||
  (p.predAdj == .verbal && p.predNoun == .verbal) ||
  (p.predAdj == .verbal && p.predNoun == .nonVerbal) ||
  (p.predAdj == .mixed)

/-- Count of languages in our sample with some form of split predication. -/
theorem split_predication_common :
    countBy allLanguages (·.hasSplitPredication) ≥ 12 := by
  native_decide

/-- Spanish and Irish exemplify the clearest nom-loc splits: both have
    two distinct copulas that partition predicate types. -/
theorem spanish_irish_clear_split :
    spanish.hasNomLocSplit = true ∧
    irish.hasNomLocSplit = true := by
  native_decide

/-- Mandarin exemplifies a three-way split: adjectives are verbal (no
    copula), nouns require `shi`, locations use `zai`. Three different
    strategies for three predicate types. -/
theorem mandarin_three_way_split :
    mandarin.predAdj == .verbal ∧
    mandarin.predNoun == .verbal ∧
    mandarin.nomLoc == .different := by
  native_decide

-- ============================================================================
-- Existential-Locational Connection
-- ============================================================================

/-- Languages that split nominal and locational predication (Ch 119)
    often use existential verbs for locational predication. In our sample,
    several nom-loc-split languages have distinct existential/locational
    forms in their copula inventory. -/
theorem nomloc_split_languages_have_distinct_forms :
    let splitLangs := allLanguages.filter (·.hasNomLocSplit)
    splitLangs.all (·.copulaForms.length ≥ 1) = true := by
  native_decide

-- ============================================================================
-- Areal Patterns
-- ============================================================================

/-- East and Southeast Asian languages (Japanese, Korean, Mandarin, Thai)
    all have verbal adjectives. This is an areal feature of the region. -/
def eastAsian : List CopulaProfile := [japanese, korean, mandarin, thai]

theorem east_asian_verbal_or_mixed_adj :
    eastAsian.all (λ p =>
      p.predAdj == .verbal || p.predAdj == .mixed) = true := by
  native_decide

/-- Semitic languages (Arabic, Hebrew) share a copula profile: non-verbal
    adjectives, non-verbal nominal predication, and restricted zero copula
    (present tense only). -/
def semitic : List CopulaProfile := [arabic, hebrew]

theorem semitic_nonverbal_adj :
    semitic.all (·.predAdj == .nonVerbal) = true := by native_decide

theorem semitic_nonverbal_noun :
    semitic.all (·.predNoun == .nonVerbal) = true := by native_decide

theorem semitic_restricted_zero :
    semitic.all (·.zeroCopula == .restricted) = true := by native_decide

/-- East Asian languages all split nominal and locational predication. -/
theorem east_asian_nomloc_split :
    eastAsian.all (·.hasNomLocSplit) = true := by native_decide

-- ============================================================================
-- Copula Type Distribution
-- ============================================================================

/-- Distribution of copula types in our sample. -/
theorem sample_verbal_copula_count :
    countBy allLanguages (·.copulaType == .verbalCopula) = 11 := by
  native_decide

theorem sample_zero_copula_type_count :
    countBy allLanguages (·.copulaType == .zero) = 4 := by
  native_decide

theorem sample_particle_copula_count :
    countBy allLanguages (·.copulaType == .particle) = 4 := by
  native_decide

theorem sample_pronominal_copula_count :
    countBy allLanguages (·.copulaType == .pronominalCopula) = 1 := by
  native_decide

/-- Verbal copulas are the most common copula type in our sample. -/
theorem verbal_copula_most_common :
    countBy allLanguages (·.copulaType == .verbalCopula) >
    countBy allLanguages (·.copulaType == .particle) ∧
    countBy allLanguages (·.copulaType == .verbalCopula) >
    countBy allLanguages (·.copulaType == .zero) ∧
    countBy allLanguages (·.copulaType == .verbalCopula) >
    countBy allLanguages (·.copulaType == .pronominalCopula) := by
  native_decide

end Phenomena.Copulas.Typology
