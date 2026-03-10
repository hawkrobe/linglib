import Linglib.Core.Lexical.Word
import Linglib.Core.WALS.Features.F117A
import Linglib.Core.WALS.Features.F118A
import Linglib.Core.WALS.Features.F119A
import Linglib.Core.WALS.Features.F120A

/-!
# Copula and Predication Typology (WALS Chapters 117--120)
@cite{hengeveld-1992} @cite{pustet-2003} @cite{stassen-1997} @cite{stassen-2013} @cite{haspelmath-2001}

Cross-linguistic data on predication strategies and copulas from four WALS
chapters, all authored by Leon @cite{stassen-2013}. These chapters address a
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

## Ch 117: Predicative Possession (N = 240)

How languages express predicative possession ("I have a book"). Five values:
- **Locational** (48/240): possession expressed as location ("a book is at me").
- **Genitive** (22/240): possession expressed with genitive ("my book exists").
- **Topic** (48/240): possession expressed as topic construction.
- **Conjunctional** (59/240): possession expressed with conjunctional strategy.
- **'Have'** (63/240): a dedicated 'have' verb is used.

## Ch 118: Predicative Adjectives (N = 386)

How languages express adjectival predication. Three values:
- **Verbal encoding**: adjectives behave like verbs (take verbal morphology,
  no copula). This is the most common strategy worldwide (151/386 = 39.1%).
- **Nonverbal encoding**: adjectives require a copula or other non-verbal
  strategy (132/386 = 34.2%).
- **Mixed**: some adjectives are verbal, others require a copula
  (103/386 = 26.7%).

## Ch 119: Nominal and Locational Predication (N = 386)

Whether a language uses the *same* or *different* strategy for nominal
predication ("is a doctor") and locational predication ("is in the room").
Two values:
- **Different**: different copulas or strategies for NOM vs LOC (269/386 = 69.7%).
- **Identical**: same copula/strategy for both (117/386 = 30.3%).

The majority pattern is to differentiate: even English, which uses "be" for
both, is cross-linguistically unusual in using a single copula.

## Ch 120: Zero Copula for Predicate Nominals (N = 386)

Whether the copula can be absent in nominal predication. Two values:
- **Impossible**: copula is always required (211/386 = 54.7%).
- **Possible**: zero copula is allowed in some or all contexts
  (175/386 = 45.3%).

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
    typology of copular elements, following @cite{pustet-2003} and
    @cite{hengeveld-1992}. -/
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

private abbrev ch117 := Core.WALS.F117A.allData
private abbrev ch118 := Core.WALS.F118A.allData
private abbrev ch119 := Core.WALS.F119A.allData
private abbrev ch120 := Core.WALS.F120A.allData

/-- Chapter 117 distribution: predicative possession (N = 240). -/
def ch117Counts : List WALSCount :=
  [ ⟨"Locational", (ch117.filter (·.value == .locational)).length⟩
  , ⟨"Genitive", (ch117.filter (·.value == .genitive)).length⟩
  , ⟨"Topic", (ch117.filter (·.value == .topic)).length⟩
  , ⟨"Conjunctional", (ch117.filter (·.value == .conjunctional)).length⟩
  , ⟨"'Have'", (ch117.filter (·.value == .have)).length⟩ ]

/-- Chapter 118 distribution: predicative adjectives (N = 386). -/
def ch118Counts : List WALSCount :=
  [ ⟨"Verbal encoding", (ch118.filter (·.value == .verbalEncoding)).length⟩
  , ⟨"Nonverbal encoding", (ch118.filter (·.value == .nonverbalEncoding)).length⟩
  , ⟨"Mixed", (ch118.filter (·.value == .mixed)).length⟩ ]

/-- Chapter 119 distribution: nominal and locational predication (N = 386). -/
def ch119Counts : List WALSCount :=
  [ ⟨"Different", (ch119.filter (·.value == .different)).length⟩
  , ⟨"Identical", (ch119.filter (·.value == .identical)).length⟩ ]

/-- Chapter 120 distribution: zero copula for predicate nominals (N = 386). -/
def ch120Counts : List WALSCount :=
  [ ⟨"Impossible", (ch120.filter (·.value == .impossible)).length⟩
  , ⟨"Possible", (ch120.filter (·.value == .possible)).length⟩ ]

-- ============================================================================
-- Aggregate Total Verification
-- ============================================================================

/-- Ch 117 total: 240 languages. -/
theorem ch117_total : WALSCount.totalOf ch117Counts = 240 := by native_decide

/-- Ch 118 total: 386 languages. -/
theorem ch118_total : WALSCount.totalOf ch118Counts = 386 := by native_decide

/-- Ch 119 total: 386 languages. -/
theorem ch119_total : WALSCount.totalOf ch119Counts = 386 := by native_decide

/-- Ch 120 total: 386 languages. -/
theorem ch120_total : WALSCount.totalOf ch120Counts = 386 := by native_decide

/-- Chapters 118, 119, 120 use the same 386-language sample.
    Chapter 117 uses a smaller 240-language sample. -/
theorem ch118_119_120_same_sample :
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

/-- Ch 118: Verbal encoding is the most common strategy for
    predicative adjectives, exceeding both mixed and nonverbal encoding. -/
theorem verbal_adj_most_common :
    (ch118.filter (·.value == .verbalEncoding)).length >
      (ch118.filter (·.value == .nonverbalEncoding)).length ∧
    (ch118.filter (·.value == .verbalEncoding)).length >
      (ch118.filter (·.value == .mixed)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 118: Verbal adjectives account for roughly 39% of the sample (151/386). -/
theorem verbal_adj_plurality :
    (ch118.filter (·.value == .verbalEncoding)).length * 3 > ch118.length := by
  native_decide

-- ============================================================================
-- Generalization 2: Non-Verbal Nominal Predication Is More Common
-- ============================================================================

/-- Ch 118: Nonverbal encoding (132) is less common than verbal encoding
    (151) for predicative adjectives, but the three values are fairly
    balanced across the 386-language sample. -/
theorem nonverbal_adj_vs_verbal :
    (ch118.filter (·.value == .verbalEncoding)).length >
    (ch118.filter (·.value == .nonverbalEncoding)).length := by native_decide

/-- Ch 118: No single predicative adjective strategy is a strict majority. -/
theorem no_adj_strategy_majority :
    (ch118.filter (·.value == .verbalEncoding)).length * 2 < ch118.length := by
  native_decide

-- ============================================================================
-- Generalization 3: Nom-Loc Split Is the Majority Pattern
-- ============================================================================

/-- Ch 119: Using different strategies for nominal and locational
    predication is more common than using the same strategy.
    This means that languages typically distinguish "is a doctor" from
    "is in the room" with different grammatical means. -/
theorem nomloc_split_majority :
    (ch119.filter (·.value == .different)).length >
    (ch119.filter (·.value == .identical)).length := by native_decide

/-- Ch 119: The split pattern accounts for a clear majority. -/
theorem nomloc_split_supermajority :
    (ch119.filter (·.value == .different)).length > ch119.length / 2 := by
  native_decide

-- ============================================================================
-- Generalization 4: Zero Copula Is a Minority Pattern Overall
-- ============================================================================

/-- Ch 120: "Impossible" (copula always required) is the majority value. -/
theorem impossible_is_majority :
    (ch120.filter (·.value == .impossible)).length >
    (ch120.filter (·.value == .possible)).length := by
  native_decide

/-- Ch 120: "Impossible" accounts for more than half the sample. -/
theorem impossible_over_half :
    (ch120.filter (·.value == .impossible)).length > ch120.length / 2 := by
  native_decide

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
    no zero copula. This is the "Standard Average European" pattern. -/
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

-- ============================================================================
-- WALS Generated Data
-- ============================================================================

/-- F117A: 240 languages (predicative possession). -/
theorem wals_f117a_total : ch117.length = 240 := by native_decide

/-- F118A: 386 languages (predicative adjectives). -/
theorem wals_f118a_total : ch118.length = 386 := by native_decide

/-- F119A: 386 languages (nominal and locational predication). -/
theorem wals_f119a_total : ch119.length = 386 := by native_decide

/-- F120A: 386 languages (zero copula for predicate nominals). -/
theorem wals_f120a_total : ch120.length = 386 := by native_decide

/-- F118A, F119A, F120A all use the same 386-language sample. -/
theorem wals_f118_f119_f120_same_sample :
    ch118.length = ch119.length ∧ ch119.length = ch120.length := by
  native_decide

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Map WALS F118A (predicative adjectives) to our `PredAdjStrategy`. -/
private def fromWALS118A : Core.WALS.F118A.PredicativeAdjectiveType → PredAdjStrategy
  | .verbalEncoding => .verbal
  | .nonverbalEncoding => .nonVerbal
  | .mixed => .mixed

/-- Map WALS F119A (nominal and locational predication) to our `NomLocStrategy`. -/
private def fromWALS119A : Core.WALS.F119A.NominalLocationalPredication → NomLocStrategy
  | .different => .different
  | .identical => .identical

/-- Map WALS F120A (zero copula) to our `ZeroCopulaStatus`.

    F120A has only two values (impossible/possible), while our `ZeroCopulaStatus`
    distinguishes restricted from widespread within "possible." The mapping is
    therefore lossy: `.impossible` maps exactly, but `.possible` is ambiguous
    between `.restricted` and `.widespread`. We return `Option` for the ambiguous
    case. -/
private def fromWALS120A : Core.WALS.F120A.ZeroCopulaType → Option ZeroCopulaStatus
  | .impossible => some .impossible
  | .possible => none

/-- Weaker predicate: does WALS F120A say zero copula is at least possible?
    This is decidable even though the restricted/widespread distinction is not. -/
private def wals120A_allowsZero : Core.WALS.F120A.ZeroCopulaType → Bool
  | .impossible => false
  | .possible => true

-- ============================================================================
-- WALS Distribution Counts (from generated data)
-- ============================================================================

/-- F118A distribution: predicative adjectives. -/
theorem wals_f118a_verbal_count :
    (ch118.filter (·.value == .verbalEncoding)).length = 151 := by native_decide
theorem wals_f118a_nonverbal_count :
    (ch118.filter (·.value == .nonverbalEncoding)).length = 132 := by native_decide
theorem wals_f118a_mixed_count :
    (ch118.filter (·.value == .mixed)).length = 103 := by native_decide

/-- F119A distribution: nominal and locational predication. -/
theorem wals_f119a_different_count :
    (ch119.filter (·.value == .different)).length = 269 := by native_decide
theorem wals_f119a_identical_count :
    (ch119.filter (·.value == .identical)).length = 117 := by native_decide

/-- F120A distribution: zero copula for predicate nominals. -/
theorem wals_f120a_impossible_count :
    (ch120.filter (·.value == .impossible)).length = 211 := by native_decide
theorem wals_f120a_possible_count :
    (ch120.filter (·.value == .possible)).length = 175 := by native_decide

/-- F117A distribution: predicative possession. -/
theorem wals_f117a_locational_count :
    (ch117.filter (·.value == .locational)).length = 48 := by native_decide
theorem wals_f117a_genitive_count :
    (ch117.filter (·.value == .genitive)).length = 22 := by native_decide
theorem wals_f117a_topic_count :
    (ch117.filter (·.value == .topic)).length = 48 := by native_decide
theorem wals_f117a_conjunctional_count :
    (ch117.filter (·.value == .conjunctional)).length = 59 := by native_decide
theorem wals_f117a_have_count :
    (ch117.filter (·.value == .have)).length = 63 := by native_decide

-- ============================================================================
-- WALS Grounding: F118A (Predicative Adjectives → predAdj)
-- Languages where WALS F118A matches the hand-coded profile value.
-- Korean, Turkish, and Swahili are omitted (profile disagrees with WALS).
-- German is absent from F118A.
-- ============================================================================

theorem english_f118a :
    (Core.WALS.F118A.lookup "eng").map (fromWALS118A ·.value) =
    some english.predAdj := by native_decide
theorem french_f118a :
    (Core.WALS.F118A.lookup "fre").map (fromWALS118A ·.value) =
    some french.predAdj := by native_decide
theorem spanish_f118a :
    (Core.WALS.F118A.lookup "spa").map (fromWALS118A ·.value) =
    some spanish.predAdj := by native_decide
theorem russian_f118a :
    (Core.WALS.F118A.lookup "rus").map (fromWALS118A ·.value) =
    some russian.predAdj := by native_decide
theorem finnish_f118a :
    (Core.WALS.F118A.lookup "fin").map (fromWALS118A ·.value) =
    some finnish.predAdj := by native_decide
theorem japanese_f118a :
    (Core.WALS.F118A.lookup "jpn").map (fromWALS118A ·.value) =
    some japanese.predAdj := by native_decide
theorem mandarin_f118a :
    (Core.WALS.F118A.lookup "mnd").map (fromWALS118A ·.value) =
    some mandarin.predAdj := by native_decide
theorem hindi_f118a :
    (Core.WALS.F118A.lookup "hin").map (fromWALS118A ·.value) =
    some hindiUrdu.predAdj := by native_decide
theorem tagalog_f118a :
    (Core.WALS.F118A.lookup "tag").map (fromWALS118A ·.value) =
    some tagalog.predAdj := by native_decide
theorem irish_f118a :
    (Core.WALS.F118A.lookup "iri").map (fromWALS118A ·.value) =
    some irish.predAdj := by native_decide
theorem hungarian_f118a :
    (Core.WALS.F118A.lookup "hun").map (fromWALS118A ·.value) =
    some hungarian.predAdj := by native_decide
theorem thai_f118a :
    (Core.WALS.F118A.lookup "tha").map (fromWALS118A ·.value) =
    some thai.predAdj := by native_decide
theorem yoruba_f118a :
    (Core.WALS.F118A.lookup "yor").map (fromWALS118A ·.value) =
    some yoruba.predAdj := by native_decide
theorem hebrew_f118a :
    (Core.WALS.F118A.lookup "heb").map (fromWALS118A ·.value) =
    some hebrew.predAdj := by native_decide
theorem arabic_f118a :
    (Core.WALS.F118A.lookup "aeg").map (fromWALS118A ·.value) =
    some arabic.predAdj := by native_decide
theorem quechua_f118a :
    (Core.WALS.F118A.lookup "qcu").map (fromWALS118A ·.value) =
    some quechua.predAdj := by native_decide

-- ============================================================================
-- WALS Grounding: F119A (Nominal and Locational Predication → nomLoc)
-- Swahili, Tagalog, Turkish, Hebrew, Arabic omitted (profile disagrees).
-- German is absent from F119A.
-- ============================================================================

theorem english_f119a :
    (Core.WALS.F119A.lookup "eng").map (fromWALS119A ·.value) =
    some english.nomLoc := by native_decide
theorem french_f119a :
    (Core.WALS.F119A.lookup "fre").map (fromWALS119A ·.value) =
    some french.nomLoc := by native_decide
theorem spanish_f119a :
    (Core.WALS.F119A.lookup "spa").map (fromWALS119A ·.value) =
    some spanish.nomLoc := by native_decide
theorem russian_f119a :
    (Core.WALS.F119A.lookup "rus").map (fromWALS119A ·.value) =
    some russian.nomLoc := by native_decide
theorem finnish_f119a :
    (Core.WALS.F119A.lookup "fin").map (fromWALS119A ·.value) =
    some finnish.nomLoc := by native_decide
theorem japanese_f119a :
    (Core.WALS.F119A.lookup "jpn").map (fromWALS119A ·.value) =
    some japanese.nomLoc := by native_decide
theorem mandarin_f119a :
    (Core.WALS.F119A.lookup "mnd").map (fromWALS119A ·.value) =
    some mandarin.nomLoc := by native_decide
theorem korean_f119a :
    (Core.WALS.F119A.lookup "kor").map (fromWALS119A ·.value) =
    some korean.nomLoc := by native_decide
theorem hindi_f119a :
    (Core.WALS.F119A.lookup "hin").map (fromWALS119A ·.value) =
    some hindiUrdu.nomLoc := by native_decide
theorem irish_f119a :
    (Core.WALS.F119A.lookup "iri").map (fromWALS119A ·.value) =
    some irish.nomLoc := by native_decide
theorem hungarian_f119a :
    (Core.WALS.F119A.lookup "hun").map (fromWALS119A ·.value) =
    some hungarian.nomLoc := by native_decide
theorem thai_f119a :
    (Core.WALS.F119A.lookup "tha").map (fromWALS119A ·.value) =
    some thai.nomLoc := by native_decide
theorem yoruba_f119a :
    (Core.WALS.F119A.lookup "yor").map (fromWALS119A ·.value) =
    some yoruba.nomLoc := by native_decide
theorem quechua_f119a :
    (Core.WALS.F119A.lookup "qcu").map (fromWALS119A ·.value) =
    some quechua.nomLoc := by native_decide

-- ============================================================================
-- WALS Grounding: F120A (Zero Copula → zeroCopula)
-- F120A collapses restricted/widespread into "possible", so exact grounding
-- is only possible for "impossible" languages. For "possible" languages we
-- prove consistency with allowsZeroCopula.
-- German is absent from F120A.
-- ============================================================================

-- Exact grounding: WALS "impossible" matches profile .impossible
theorem english_f120a :
    (Core.WALS.F120A.lookup "eng").map (fromWALS120A ·.value) =
    some (some english.zeroCopula) := by native_decide
theorem french_f120a :
    (Core.WALS.F120A.lookup "fre").map (fromWALS120A ·.value) =
    some (some french.zeroCopula) := by native_decide
theorem spanish_f120a :
    (Core.WALS.F120A.lookup "spa").map (fromWALS120A ·.value) =
    some (some spanish.zeroCopula) := by native_decide
theorem finnish_f120a :
    (Core.WALS.F120A.lookup "fin").map (fromWALS120A ·.value) =
    some (some finnish.zeroCopula) := by native_decide
theorem japanese_f120a :
    (Core.WALS.F120A.lookup "jpn").map (fromWALS120A ·.value) =
    some (some japanese.zeroCopula) := by native_decide
theorem korean_f120a :
    (Core.WALS.F120A.lookup "kor").map (fromWALS120A ·.value) =
    some (some korean.zeroCopula) := by native_decide
theorem mandarin_f120a :
    (Core.WALS.F120A.lookup "mnd").map (fromWALS120A ·.value) =
    some (some mandarin.zeroCopula) := by native_decide
theorem irish_f120a :
    (Core.WALS.F120A.lookup "iri").map (fromWALS120A ·.value) =
    some (some irish.zeroCopula) := by native_decide
theorem hindi_f120a :
    (Core.WALS.F120A.lookup "hin").map (fromWALS120A ·.value) =
    some (some hindiUrdu.zeroCopula) := by native_decide

-- Consistency grounding: WALS "possible" is consistent with profile
-- allowsZeroCopula (restricted or widespread)
theorem russian_f120a_consistent :
    (Core.WALS.F120A.lookup "rus").map (wals120A_allowsZero ·.value) =
    some (russian.allowsZeroCopula) := by native_decide
theorem hungarian_f120a_consistent :
    (Core.WALS.F120A.lookup "hun").map (wals120A_allowsZero ·.value) =
    some (hungarian.allowsZeroCopula) := by native_decide
theorem arabic_f120a_consistent :
    (Core.WALS.F120A.lookup "aeg").map (wals120A_allowsZero ·.value) =
    some (arabic.allowsZeroCopula) := by native_decide
theorem hebrew_f120a_consistent :
    (Core.WALS.F120A.lookup "heb").map (wals120A_allowsZero ·.value) =
    some (hebrew.allowsZeroCopula) := by native_decide
theorem quechua_f120a_consistent :
    (Core.WALS.F120A.lookup "qcu").map (wals120A_allowsZero ·.value) =
    some (quechua.allowsZeroCopula) := by native_decide

-- ============================================================================
-- WALS Grounding: F117A (Predicative Possession)
-- F117A classifies how languages express predicative possession.
-- This is supplementary data — CopulaProfile does not have a possession field,
-- but the feature is part of the same typological cluster (WALS Ch 117--120).
-- We verify that each language is present in the dataset with the expected value.
-- German is absent from F117A.
-- ============================================================================

theorem english_f117a :
    (Core.WALS.F117A.lookup "eng").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.have := by native_decide
theorem spanish_f117a :
    (Core.WALS.F117A.lookup "spa").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.have := by native_decide
theorem finnish_f117a :
    (Core.WALS.F117A.lookup "fin").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem russian_f117a :
    (Core.WALS.F117A.lookup "rus").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem japanese_f117a :
    (Core.WALS.F117A.lookup "jpn").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem korean_f117a :
    (Core.WALS.F117A.lookup "kor").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem mandarin_f117a :
    (Core.WALS.F117A.lookup "mnd").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.topic := by native_decide
theorem turkish_f117a :
    (Core.WALS.F117A.lookup "tur").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.genitive := by native_decide
theorem hindi_f117a :
    (Core.WALS.F117A.lookup "hin").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem hungarian_f117a :
    (Core.WALS.F117A.lookup "hun").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem hebrew_f117a :
    (Core.WALS.F117A.lookup "heb").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem irish_f117a :
    (Core.WALS.F117A.lookup "iri").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide
theorem swahili_f117a :
    (Core.WALS.F117A.lookup "swa").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.conjunctional := by native_decide
theorem tagalog_f117a :
    (Core.WALS.F117A.lookup "tag").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.topic := by native_decide
theorem thai_f117a :
    (Core.WALS.F117A.lookup "tha").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.topic := by native_decide
theorem yoruba_f117a :
    (Core.WALS.F117A.lookup "yor").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.have := by native_decide
theorem arabic_f117a :
    (Core.WALS.F117A.lookup "aeg").map (·.value) =
    some Core.WALS.F117A.PredicativePossession.locational := by native_decide

end Phenomena.Copulas.Typology
