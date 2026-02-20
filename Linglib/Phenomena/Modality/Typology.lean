import Linglib.Core.Basic

/-!
# Cross-Linguistic Typology of Evidentiality (WALS Chapters 77--78)

Cross-linguistic data on grammatical evidentiality from the World Atlas of
Language Structures, covering two parameters:

- **Ch 77: Semantic Distinctions of Evidentiality** (de Haan 2013a): How many
  and which evidential distinctions a language grammaticalizes. Evidentials
  encode the speaker's source of information for a proposition --- whether they
  witnessed it directly, inferred it from indirect evidence, or received it via
  report. Languages range from no grammatical evidentials at all (English,
  Mandarin) to systems with three or more obligatory distinctions (Tuyuca,
  Quechua). The majority of the world's languages (181/318 = 57%) lack
  grammatical evidentials entirely.

- **Ch 78: Coding of Evidentiality** (de Haan 2013b): How evidentiality is
  morphologically expressed in languages that have it. Four strategies: verbal
  affix (the dominant pattern, 131/191 = 69%), clitic, modal particle, or
  fusion with the TAM (tense-aspect-mood) system. Only languages with
  grammatical evidentials are included in this chapter.

## Key findings

De Haan (2013) observes that evidentiality is areally concentrated: it is
pervasive in the Americas (especially the Andes and Amazonia), common across
Central and Inner Asia (Tibetan, Turkic), and well-attested in the Balkans
and Caucasus. In other parts of the world --- most of Africa, most of
Western Europe, most of East Asia --- grammatical evidentials are absent.
When present, evidentials are overwhelmingly verbal affixes; particles and
clitics are comparatively rare. Systems with three or more evidential choices
always include direct evidence as a grammaticalized category.

## References

- de Haan, F. (2013a). Semantic Distinctions of Evidentiality. In Dryer &
  Haspelmath (eds.), WALS Online (v2020.3). https://wals.info/chapter/77
- de Haan, F. (2013b). Coding of Evidentiality. In Dryer & Haspelmath
  (eds.), WALS Online (v2020.3). https://wals.info/chapter/78
- Aikhenvald, A. Y. (2004). Evidentiality. Oxford University Press.
- de Haan, F. (1999). Evidentiality and epistemic modality: Setting
  boundaries. Southwest Journal of Linguistics 18: 83--101.
- Willett, T. (1988). A cross-linguistic survey of the grammaticalization
  of evidentiality. Studies in Language 12: 51--97.
-/

namespace Phenomena.Modality.Typology

-- ============================================================================
-- Chapter 77: Semantic Distinctions of Evidentiality
-- ============================================================================

/-- WALS Ch 77: How many evidential distinctions a language grammaticalizes.

    Four values on a scale of increasing complexity:
    (1) No grammatical evidentials: evidential source is conveyed lexically
        or pragmatically, never by obligatory morphology.
    (2) Indirect evidential only: the language has a single evidential marker
        indicating indirect (reported, inferred, or both) information source,
        but no dedicated marker for direct evidence.
    (3) Two-choice system (direct vs indirect): the language distinguishes
        direct evidence (visual/sensory witness) from indirect evidence
        (reportative, inferential, or both).
    (4) Three-or-more-choice system: the language distinguishes at least
        direct, reportative, and inferential evidence as separate categories.
        May include further distinctions (visual vs nonvisual, firsthand vs
        secondhand report, assumption vs inference from results). -/
inductive EvidentialSystem where
  /-- No grammatical evidentials. Evidential source may be conveyed by
      lexical adverbs ("apparently", "reportedly") or pragmatic inference,
      but is never obligatorily encoded in verbal morphology.
      (e.g., English, French, Mandarin, German) -/
  | noGrammatical
  /-- Indirect evidential only. A single marker indicates that the
      speaker's information comes from a non-direct source (inference,
      report, or both), with no dedicated direct-evidence marker.
      (e.g., Georgian, Tajik, West Greenlandic) -/
  | indirectOnly
  /-- Two-choice system: direct vs indirect evidence. The language
      obligatorily distinguishes firsthand sensory witness from all
      other information sources.
      (e.g., Turkish, Bulgarian, Tibetan, Abkhaz) -/
  | directAndIndirect
  /-- Three or more evidential choices. The language distinguishes
      at least direct, reportative, and inferential as separate
      grammatical categories. May include further splits.
      (e.g., Quechua, Tuyuca, Kashaya, Aymara) -/
  | threeOrMore
  deriving DecidableEq, BEq, Repr

/-- Whether a language has any grammatical evidential marking. -/
def EvidentialSystem.hasEvidentials : EvidentialSystem -> Bool
  | .noGrammatical => false
  | .indirectOnly | .directAndIndirect | .threeOrMore => true

/-- Whether a language grammaticalizes a direct evidence category. -/
def EvidentialSystem.hasDirect : EvidentialSystem -> Bool
  | .directAndIndirect | .threeOrMore => true
  | .noGrammatical | .indirectOnly => false

/-- Number of evidential choices in the system (0, 1, 2, or 3+). -/
def EvidentialSystem.numChoices : EvidentialSystem -> Nat
  | .noGrammatical => 0
  | .indirectOnly => 1
  | .directAndIndirect => 2
  | .threeOrMore => 3

-- ============================================================================
-- Chapter 78: Coding of Evidentiality
-- ============================================================================

/-- WALS Ch 78: How evidentiality is morphologically expressed.

    Only applicable to languages that HAVE grammatical evidentials.
    Four coding strategies:
    (1) Verbal affix: evidential is a bound morpheme on the verb.
    (2) Clitic: evidential is a clitic (phrasal affix, not bound to verb).
    (3) Modal particle: evidential is a free-standing particle.
    (4) Part of the TAM system: evidential distinctions are fused with
        tense-aspect-mood marking and cannot be separated. -/
inductive EvidentialCoding where
  /-- Evidential is a verbal affix (bound morpheme on the verb stem).
      The dominant strategy worldwide (131/191 = 69%).
      (e.g., Quechua ‑mi, ‑si, ‑chá; Turkish ‑mIş; Tuyuca verbal suffixes) -/
  | verbalAffix
  /-- Evidential is a clitic (phrasal-level bound morpheme, not specific
      to the verb). Relatively rare (10/191 = 5%).
      (e.g., Tsafiki =ti, Kham =re) -/
  | clitic
  /-- Evidential is a free modal particle. Uncommon (19/191 = 10%).
      (e.g., Lhasa Tibetan 'dug, Kalmyk gej) -/
  | particle
  /-- Evidential distinctions are fused into the tense-aspect-mood
      paradigm and cannot be isolated as a separate morpheme.
      (e.g., Bulgarian, Georgian, Abkhaz, some Turkic languages) -/
  | partOfTAM
  /-- Not applicable: language has no grammatical evidentials (Ch 77
      value 1). Used for cross-chapter profile consistency. -/
  | notApplicable
  deriving DecidableEq, BEq, Repr

/-- Whether the coding strategy involves a bound morpheme (affix or clitic). -/
def EvidentialCoding.isBound : EvidentialCoding -> Bool
  | .verbalAffix | .clitic => true
  | .particle | .partOfTAM | .notApplicable => false

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

/-- Chapter 77 distribution: semantic distinctions of evidentiality (N = 318). -/
def ch77Counts : List WALSCount :=
  [ ⟨"No grammatical evidentials", 181⟩
  , ⟨"Indirect evidential only", 38⟩
  , ⟨"Direct and indirect", 71⟩
  , ⟨"Direct, indirect, and other", 28⟩ ]

/-- Chapter 78 distribution: coding of evidentiality (N = 191).
    Only languages with grammatical evidentials are included.
    Note: 191 = 318 - 181 + some overlap differences due to slightly
    different sampling; the samples overlap but are not identical. -/
def ch78Counts : List WALSCount :=
  [ ⟨"Verbal affix", 131⟩
  , ⟨"Clitic", 10⟩
  , ⟨"Modal particle", 19⟩
  , ⟨"Part of the tense system", 31⟩ ]

-- ============================================================================
-- Aggregate Total Verification
-- ============================================================================

/-- Ch 77 total: 318 languages. -/
theorem ch77_total : WALSCount.totalOf ch77Counts = 318 := by native_decide

/-- Ch 78 total: 191 languages. -/
theorem ch78_total : WALSCount.totalOf ch78Counts = 191 := by native_decide

/-- Ch 78 sample size is smaller than Ch 77, since Ch 78 excludes languages
    without grammatical evidentials. -/
theorem ch78_subset_of_ch77 :
    WALSCount.totalOf ch78Counts < WALSCount.totalOf ch77Counts := by
  native_decide

-- ============================================================================
-- Evidentiality Profile Structure
-- ============================================================================

/-- A language's evidentiality profile across WALS Chapters 77--78. -/
structure EvidentialityProfile where
  /-- Language name -/
  language : String
  /-- ISO 639-3 code -/
  iso : String
  /-- Language family -/
  family : String
  /-- WALS Ch 77: evidential system type -/
  system : EvidentialSystem
  /-- WALS Ch 78: coding strategy -/
  coding : EvidentialCoding
  /-- Evidential marker forms (if applicable) -/
  markers : List String := []
  /-- Notes on the evidential system -/
  notes : String := ""
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Language Data
-- ============================================================================

/--
English (Indo-European, Germanic).
No grammatical evidentials. Evidential source is conveyed lexically by
adverbs like "apparently", "reportedly", "evidently", or by hedging
expressions like "I hear that...", "it seems that...". None of these
are obligatory or part of the verbal paradigm.
-/
def english : EvidentialityProfile :=
  { language := "English", iso := "eng", family := "Indo-European"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "Lexical evidentials only: apparently, reportedly, evidently" }

/--
French (Indo-European, Romance).
No grammatical evidentials. The conditional tense can convey reportative
meaning in journalistic French ("le president serait malade" — 'the
president is reportedly sick'), but this is not a dedicated evidential
marker; it is a secondary use of the conditional.
-/
def french : EvidentialityProfile :=
  { language := "French", iso := "fra", family := "Indo-European"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "Conditional has secondary reportative use in journalistic register" }

/--
German (Indo-European, Germanic).
No grammatical evidentials. The modal verbs "sollen" (reportative) and
"wollen" (self-report) have evidential-like uses but are full modal verbs,
not grammaticalized evidential markers.
-/
def german : EvidentialityProfile :=
  { language := "German", iso := "deu", family := "Indo-European"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "sollen/wollen have evidential uses but are modal verbs" }

/--
Mandarin Chinese (Sino-Tibetan).
No grammatical evidentials. Evidential source is conveyed by lexical items
such as "tinshuo" (听说, 'I hear that'), "juede" (觉得, 'I feel that'),
or sentence-final particles like "ba" (吧) for tentativeness.
-/
def mandarin : EvidentialityProfile :=
  { language := "Mandarin", iso := "cmn", family := "Sino-Tibetan"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "Lexical evidential strategies: tinshuo, juede; no obligatory marking" }

/--
Japanese (Japonic).
No grammatical evidentials in the strict sense. The hearsay particle
"soo da" (そうだ) and inferential "rashii" (らしい) have evidential-like
functions but are analyzed as modal rather than evidential morphology by
de Haan (2013). WALS classifies Japanese as lacking grammatical evidentials.
-/
def japanese : EvidentialityProfile :=
  { language := "Japanese", iso := "jpn", family := "Japonic"
  , system := .noGrammatical, coding := .notApplicable
  , markers := ["soo da", "rashii"]
  , notes := "soo da (hearsay) and rashii (inferential) are modal, not " ++
             "grammaticalized evidentials per de Haan (2013)" }

/--
Korean (Koreanic).
No grammatical evidentials. Korean has evidential-like constructions
(e.g., "-deo-" retrospective, "-da-" reported speech) but these are
not classified as grammaticalized evidentials in WALS.
-/
def korean : EvidentialityProfile :=
  { language := "Korean", iso := "kor", family := "Koreanic"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "-deo- (retrospective) has evidential-like function but is " ++
             "not classified as grammatical evidential in WALS" }

/--
Turkish (Turkic).
Two-choice evidential system: direct vs indirect. The past tense paradigm
contrasts direct-evidence past (-DI, witnessed) with indirect-evidence past
(-mIş, inferred or reported). The -mIş suffix is the best-known example
of an indirect evidential in a major language. The distinction is obligatory
in past-tense contexts. Coded as part of the TAM system (evidentiality is
fused with past tense).
-/
def turkish : EvidentialityProfile :=
  { language := "Turkish", iso := "tur", family := "Turkic"
  , system := .directAndIndirect, coding := .partOfTAM
  , markers := ["-DI (direct)", "-mIş (indirect)"]
  , notes := "Evidential distinction fused with past tense; -DI = witnessed, " ++
             "-mIş = inferred/reported" }

/--
Bulgarian (Indo-European, Slavic).
Two-choice evidential system: direct (witnessed) vs indirect
(reported, nonwitnessed). Bulgarian is the best-known European language
with grammatical evidentials. The distinction is marked by a contrast
between the aorist (direct/witnessed) and a separate evidential paradigm
(indirect/nonwitnessed). Fused with the TAM system.
-/
def bulgarian : EvidentialityProfile :=
  { language := "Bulgarian", iso := "bul", family := "Indo-European"
  , system := .directAndIndirect, coding := .partOfTAM
  , markers := ["aorist (direct)", "l-form (indirect)"]
  , notes := "Balkan evidentiality; direct (aorist) vs indirect (l-participle " ++
             "based forms); fused with tense-aspect" }

/--
Tibetan (Sino-Tibetan, Tibeto-Burman).
Two-choice evidential system: direct (egophoric/sensory) vs indirect.
Lhasa Tibetan uses the copula/auxiliary contrast: "red" and "yod" for
personal knowledge/direct evidence, "yin" and "'dug" for indirect/new
information. The evidential markers are particles/auxiliaries.
-/
def tibetan : EvidentialityProfile :=
  { language := "Tibetan (Lhasa)", iso := "bod", family := "Sino-Tibetan"
  , system := .directAndIndirect, coding := .particle
  , markers := ["red (direct)", "'dug (indirect)", "yod (direct)", "yin (indirect)"]
  , notes := "Egophoric system; direct/personal knowledge vs indirect/new info; " ++
             "expressed via copula and auxiliary contrasts" }

/--
Georgian (Kartvelian).
Indirect evidential only. Georgian has an evidential perfect (the "I
screeve") that marks the proposition as based on inference or report,
but has no dedicated direct-evidence marker. The evidential distinction
is fused with the TAM system (part of the verbal screeve paradigm).
-/
def georgian : EvidentialityProfile :=
  { language := "Georgian", iso := "kat", family := "Kartvelian"
  , system := .indirectOnly, coding := .partOfTAM
  , markers := ["evidential perfect (I screeve)"]
  , notes := "Evidential perfect for inference/report; no dedicated direct marker; " ++
             "fused with tense-aspect screeve system" }

/--
Quechua (Cuzco) (Quechuan).
Three-or-more-choice system: direct (‑mi, ‑n), reportative (‑si, ‑s), and
conjectural (‑chá). The three enclitics are obligatory on
finite clauses and encode the speaker's information source. Quechua is
one of the canonical examples of a three-way evidential system.
Coded as verbal affixes (enclitics on the verb or predicate).
-/
def quechua : EvidentialityProfile :=
  { language := "Quechua (Cuzco)", iso := "quz", family := "Quechuan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-mi (direct)", "-si (reportative)", "-chá (conjectural)"]
  , notes := "Canonical three-way system: direct/reportative/conjectural; " ++
             "obligatory on finite clauses" }

/--
Aymara (Aymaran).
Three-or-more-choice system: direct/personal knowledge, reportative, and
non-personal knowledge (inferential). Like Quechua, Aymara has obligatory
evidential suffixes marking information source. Coded as verbal affixes.
-/
def aymara : EvidentialityProfile :=
  { language := "Aymara", iso := "aym", family := "Aymaran"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-wa (direct)", "-sa (reportative)", "-pacha (inferential)"]
  , notes := "Obligatory three-way system; Andean areal feature shared " ++
             "with Quechua" }

/--
Tuyuca (Tucanoan).
Three-or-more-choice system with one of the richest evidential inventories
known: five evidential categories --- visual, nonvisual sensory, apparent
(inferential), secondhand (reported), and assumed. All five are
obligatorily encoded as verbal suffixes. Barnes (1984) is the classic
description. Coded as verbal affixes.
-/
def tuyuca : EvidentialityProfile :=
  { language := "Tuyuca", iso := "tue", family := "Tucanoan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-wi (visual)", "-ti (nonvisual)", "-yi (apparent)",
                "-yigi (secondhand)", "-hiyi (assumed)"]
  , notes := "Five-way evidential system: visual/nonvisual/apparent/" ++
             "secondhand/assumed; obligatory verbal suffixes; " ++
             "Barnes (1984)" }

/--
Kashaya (Pomoan).
Three-or-more-choice system: performative/factual (direct), visual,
auditory, inferential, and reportative. Coded as verbal suffixes. Kashaya
is notable for distinguishing visual from auditory direct evidence.
Oswalt (1986) is the primary source.
-/
def kashaya : EvidentialityProfile :=
  { language := "Kashaya", iso := "kju", family := "Pomoan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-ya (performative)", "-ʔ (visual)", "-inne (auditory)",
                "-qa (inferential)", "-do (reportative)"]
  , notes := "Four-way sensory+inferential+reportative; distinguishes " ++
             "visual from auditory direct evidence; Oswalt (1986)" }

/--
Tariana (Arawakan).
Three-or-more-choice system with five evidential categories: visual,
nonvisual, inferred, assumed, and reported. Like Tuyuca, Tariana has a
five-way system. It is spoken in the multilingual Vaupés area of Brazil
where elaborate evidential systems are an areal feature. Verbal affixes.
-/
def tariana : EvidentialityProfile :=
  { language := "Tariana", iso := "tae", family := "Arawakan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-ka (visual)", "-mha (nonvisual)", "-nihka (inferred)",
                "-sika (assumed)", "-pidaka (reported)"]
  , notes := "Five-way system; Vaupés multilingual area; " ++
             "Aikhenvald (2003, 2004)" }

/--
West Greenlandic (Eskimo-Aleut).
Indirect evidential only. West Greenlandic has an inferential mood
(expressed by verbal suffixes) but no grammaticalized direct-evidence
marker. The speaker uses the inferential when the proposition is based
on reasoning from observable effects.
-/
def westGreenlandic : EvidentialityProfile :=
  { language := "West Greenlandic", iso := "kal", family := "Eskimo-Aleut"
  , system := .indirectOnly, coding := .verbalAffix
  , markers := ["-gunarpoq (inferential mood)"]
  , notes := "Inferential mood only; no dedicated direct marker" }

/--
Abkhaz (Northwest Caucasian).
Two-choice system: direct (witnessed) vs indirect (nonwitnessed/reported).
The evidential distinction is part of the complex verbal morphology and is
fused with tense-aspect marking.
-/
def abkhaz : EvidentialityProfile :=
  { language := "Abkhaz", iso := "abk", family := "Northwest Caucasian"
  , system := .directAndIndirect, coding := .partOfTAM
  , markers := ["finite verb (direct)", "nonfinite + copula (indirect)"]
  , notes := "Evidential fused with tense-aspect; Caucasus areal feature" }

/-- All language profiles in the sample. -/
def allLanguages : List EvidentialityProfile :=
  [ english, french, german, mandarin, japanese, korean
  , turkish, bulgarian, tibetan
  , georgian, westGreenlandic
  , quechua, aymara, tuyuca, kashaya, tariana
  , abkhaz ]

-- ============================================================================
-- Helper Predicates
-- ============================================================================

/-- Does a language have grammatical evidentials? -/
def EvidentialityProfile.hasEvidentials (p : EvidentialityProfile) : Bool :=
  p.system.hasEvidentials

/-- Does a language have a direct evidence category? -/
def EvidentialityProfile.hasDirect (p : EvidentialityProfile) : Bool :=
  p.system.hasDirect

/-- Count of languages in the sample with a given system type. -/
def countBySystem (langs : List EvidentialityProfile) (s : EvidentialSystem) : Nat :=
  (langs.filter (·.system == s)).length

/-- Count of languages in the sample with a given coding type. -/
def countByCoding (langs : List EvidentialityProfile) (c : EvidentialCoding) : Nat :=
  (langs.filter (·.coding == c)).length

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Languages without evidentials
example : english.system = .noGrammatical := by native_decide
example : french.system = .noGrammatical := by native_decide
example : german.system = .noGrammatical := by native_decide
example : mandarin.system = .noGrammatical := by native_decide
example : japanese.system = .noGrammatical := by native_decide
example : korean.system = .noGrammatical := by native_decide

-- Languages with indirect evidential only
example : georgian.system = .indirectOnly := by native_decide
example : westGreenlandic.system = .indirectOnly := by native_decide

-- Languages with two-choice (direct + indirect) systems
example : turkish.system = .directAndIndirect := by native_decide
example : bulgarian.system = .directAndIndirect := by native_decide
example : tibetan.system = .directAndIndirect := by native_decide
example : abkhaz.system = .directAndIndirect := by native_decide

-- Languages with three-or-more-choice systems
example : quechua.system = .threeOrMore := by native_decide
example : aymara.system = .threeOrMore := by native_decide
example : tuyuca.system = .threeOrMore := by native_decide
example : kashaya.system = .threeOrMore := by native_decide
example : tariana.system = .threeOrMore := by native_decide

-- Coding verification
example : english.coding = .notApplicable := by native_decide
example : turkish.coding = .partOfTAM := by native_decide
example : bulgarian.coding = .partOfTAM := by native_decide
example : tibetan.coding = .particle := by native_decide
example : quechua.coding = .verbalAffix := by native_decide
example : tuyuca.coding = .verbalAffix := by native_decide
example : georgian.coding = .partOfTAM := by native_decide

-- ============================================================================
-- Sample Size
-- ============================================================================

/-- Number of languages in our sample. -/
theorem sample_size : allLanguages.length = 17 := by native_decide

-- ============================================================================
-- Typological Generalization 1: Most Languages Lack Grammatical Evidentials
-- ============================================================================

/-- Ch 77: The majority of languages (181/318 = 57%) lack grammatical
    evidentials entirely. This is the single largest category. -/
theorem no_evidentials_most_common :
    (181 : Nat) > 38 ∧ (181 : Nat) > 71 ∧ (181 : Nat) > 28 := by
  native_decide

/-- Ch 77: Languages without grammatical evidentials outnumber all languages
    WITH evidentials combined (181 vs 137). -/
theorem no_evidentials_majority : (181 : Nat) > 38 + 71 + 28 := by
  native_decide

/-- In our sample, over a third of languages lack grammatical evidentials
    (6 out of 17). The sample deliberately overrepresents languages with
    evidentials for typological diversity. -/
theorem sample_no_evidentials_count :
    countBySystem allLanguages .noGrammatical = 6 := by
  native_decide

-- ============================================================================
-- Typological Generalization 2: Verbal Affix Is the Dominant Coding Strategy
-- ============================================================================

/-- Ch 78: Verbal affix (131/191 = 69%) is by far the most common way to
    encode evidentiality. It outnumbers all other strategies combined. -/
theorem verbal_affix_dominant :
    (131 : Nat) > 10 + 19 + 31 := by native_decide

/-- Ch 78: Verbal affixes account for more than two-thirds of all
    evidential coding strategies. -/
theorem verbal_affix_supermajority :
    (131 : Nat) * 3 > (131 + 10 + 19 + 31) * 2 := by native_decide

/-- Ch 78: Clitics are the rarest evidential coding strategy (10/191). -/
theorem clitics_rarest :
    (10 : Nat) < 19 ∧ (10 : Nat) < 31 ∧ (10 : Nat) < 131 := by
  native_decide

-- ============================================================================
-- Typological Generalization 3: Two-Choice Systems Are More Common Than
-- Three-or-More-Choice Systems
-- ============================================================================

/-- Ch 77: Among languages with evidentials, two-choice (direct vs indirect)
    systems (71) are more common than three-or-more-choice systems (28). -/
theorem two_choice_more_common_than_three :
    (71 : Nat) > 28 := by native_decide

/-- Ch 77: Two-choice systems are also more common than indirect-only
    systems (71 vs 38). -/
theorem two_choice_more_common_than_indirect_only :
    (71 : Nat) > 38 := by native_decide

/-- Ch 77: Two-choice systems are the most common type among languages
    that HAVE evidentials. -/
theorem two_choice_most_common_with_evidentials :
    (71 : Nat) > 38 ∧ (71 : Nat) > 28 := by native_decide

-- ============================================================================
-- Typological Generalization 4: Three-or-More Systems Always Include Direct
-- ============================================================================

/-- Languages with three or more evidential choices always include a direct
    evidence category. This follows from the definition: three-choice systems
    distinguish direct, reportative, and inferential. No language is known
    to have three evidential categories without including direct evidence.

    In our sample, every three-or-more language has a direct category. -/
theorem three_or_more_always_has_direct :
    let threeOrMore := allLanguages.filter (·.system == .threeOrMore)
    threeOrMore.all (·.hasDirect) = true := by
  native_decide

/-- The converse does not hold: two-choice systems also have direct evidence.
    In fact, in our sample, every language with direct evidence has either a
    two-choice or three-or-more system. -/
theorem direct_implies_at_least_two_choices :
    let withDirect := allLanguages.filter (·.hasDirect)
    withDirect.all (λ p => p.system == .directAndIndirect ||
                           p.system == .threeOrMore) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 5: TAM Fusion in Balkan and Caucasus Languages
-- ============================================================================

/-- Evidentiality fused with the TAM system is characteristic of the
    Balkans and Caucasus. In our sample, Turkish, Bulgarian, Georgian,
    and Abkhaz all use TAM-fused evidentials. -/
theorem tam_fusion_in_sample :
    turkish.coding = .partOfTAM ∧
    bulgarian.coding = .partOfTAM ∧
    georgian.coding = .partOfTAM ∧
    abkhaz.coding = .partOfTAM := by
  native_decide

/-- TAM fusion is the second most common coding strategy after verbal
    affixes (31/191 = 16%). -/
theorem tam_fusion_second_most_common :
    (31 : Nat) > 19 ∧ (31 : Nat) > 10 := by native_decide

-- ============================================================================
-- Typological Generalization 6: Andean Areal Feature
-- ============================================================================

/-- Quechua and Aymara, the two major Andean language families, both have
    three-or-more-choice evidential systems coded as verbal affixes.
    This is a well-known areal feature of the Andes. -/
theorem andean_evidential_cluster :
    quechua.system = .threeOrMore ∧ aymara.system = .threeOrMore ∧
    quechua.coding = .verbalAffix ∧ aymara.coding = .verbalAffix := by
  native_decide

-- ============================================================================
-- Typological Generalization 7: Amazonian Rich Evidential Systems
-- ============================================================================

/-- The Vaupés-Amazonian area has some of the richest evidential systems.
    Both Tuyuca and Tariana (from different families but in contact in the
    Vaupés) have three-or-more evidential categories with five distinctions.
    This suggests areal diffusion of complex evidential systems. -/
theorem amazonian_rich_systems :
    tuyuca.system = .threeOrMore ∧ tariana.system = .threeOrMore ∧
    tuyuca.coding = .verbalAffix ∧ tariana.coding = .verbalAffix := by
  native_decide

-- ============================================================================
-- Typological Generalization 8: Indirect-Only Systems Are Uncommon
-- ============================================================================

/-- Ch 77: Indirect-only systems (38 languages) are the least common type
    among languages WITH evidentials (vs 71 two-choice and 28 three-choice).
    These are languages that only mark non-direct evidence, leaving direct
    evidence unmarked. -/
theorem indirect_only_least_common_among_evidentials :
    (38 : Nat) < 71 := by native_decide

/-- In our sample, exactly 2 languages have indirect-only systems. -/
theorem sample_indirect_only_count :
    countBySystem allLanguages .indirectOnly = 2 := by native_decide

-- ============================================================================
-- Typological Generalization 9: Verbal Affix Among Three-or-More Systems
-- ============================================================================

/-- In our sample, all languages with three-or-more evidential choices
    use verbal affixes as their coding strategy. This is consistent with
    the cross-linguistic generalization that complex evidential systems
    tend to use morphologically integrated (affixal) coding. -/
theorem complex_systems_use_affixes :
    let complex := allLanguages.filter (·.system == .threeOrMore)
    complex.all (·.coding == .verbalAffix) = true := by
  native_decide

-- ============================================================================
-- Typological Generalization 10: Western European Languages Lack Evidentials
-- ============================================================================

/-- In our sample, the three Western European languages (English, French,
    German) all lack grammatical evidentials. This is consistent with the
    broader pattern: grammatical evidentials are essentially absent from
    Western Europe (the Balkan Sprachbund is the notable exception). -/
def westernEuropean : List EvidentialityProfile := [english, french, german]

theorem western_european_no_evidentials :
    westernEuropean.all (·.system == .noGrammatical) = true := by
  native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-- In our sample, every language without grammatical evidentials (Ch 77)
    has a notApplicable coding (Ch 78). -/
theorem no_evidentials_implies_na_coding :
    let noEvid := allLanguages.filter (·.system == .noGrammatical)
    noEvid.all (·.coding == .notApplicable) = true := by
  native_decide

/-- In our sample, every language WITH grammatical evidentials has a
    real (non-notApplicable) coding strategy. -/
theorem evidentials_implies_real_coding :
    let withEvid := allLanguages.filter (·.hasEvidentials)
    withEvid.all (·.coding != .notApplicable) = true := by
  native_decide

/-- The system and coding fields are consistent: the set of languages with
    notApplicable coding is exactly the set with noGrammatical system. -/
theorem system_coding_consistency :
    allLanguages.all (λ p =>
      (p.system == .noGrammatical) == (p.coding == .notApplicable)) = true := by
  native_decide

-- ============================================================================
-- Summary Statistics for Our Sample
-- ============================================================================

/-- System type distribution in our sample. -/
theorem sample_system_counts :
    countBySystem allLanguages .noGrammatical = 6 ∧
    countBySystem allLanguages .indirectOnly = 2 ∧
    countBySystem allLanguages .directAndIndirect = 4 ∧
    countBySystem allLanguages .threeOrMore = 5 := by
  native_decide

/-- Coding strategy distribution in our sample (excluding notApplicable). -/
theorem sample_coding_counts :
    countByCoding allLanguages .verbalAffix = 6 ∧
    countByCoding allLanguages .clitic = 0 ∧
    countByCoding allLanguages .particle = 1 ∧
    countByCoding allLanguages .partOfTAM = 4 ∧
    countByCoding allLanguages .notApplicable = 6 := by
  native_decide

/-- Languages with evidentials in our sample. -/
theorem sample_has_evidentials_count :
    (allLanguages.filter (·.hasEvidentials)).length = 11 := by
  native_decide

/-- Languages with direct evidence marking in our sample. -/
theorem sample_has_direct_count :
    (allLanguages.filter (·.hasDirect)).length = 9 := by
  native_decide

-- ============================================================================
-- Implicational Hierarchy
-- ============================================================================

/-- The evidential complexity hierarchy: more evidential categories imply
    at least as many categories as simpler systems. In our sample:

    threeOrMore.numChoices > directAndIndirect.numChoices >
    indirectOnly.numChoices > noGrammatical.numChoices -/
theorem evidential_complexity_hierarchy :
    EvidentialSystem.numChoices .threeOrMore >
    EvidentialSystem.numChoices .directAndIndirect ∧
    EvidentialSystem.numChoices .directAndIndirect >
    EvidentialSystem.numChoices .indirectOnly ∧
    EvidentialSystem.numChoices .indirectOnly >
    EvidentialSystem.numChoices .noGrammatical := by
  native_decide

/-- In our sample, every language with a three-or-more system also has a
    direct evidence category (entailed by the type definition, but worth
    verifying against the data). -/
theorem three_or_more_implies_direct_in_sample :
    allLanguages.all (λ p =>
      p.system == .threeOrMore → p.hasDirect = true) = true := by
  native_decide

/-- In our sample, every language with a two-choice system also has a
    direct evidence category (the two choices are direct vs indirect). -/
theorem two_choice_implies_direct_in_sample :
    let twoChoice := allLanguages.filter (·.system == .directAndIndirect)
    twoChoice.all (·.hasDirect) = true := by
  native_decide

-- ============================================================================
-- Areal Patterns
-- ============================================================================

/-- East Asian languages in our sample (Mandarin, Japanese, Korean) all lack
    grammatical evidentials. This is consistent with the broader pattern that
    East Asia is an evidential-free zone. -/
def eastAsian : List EvidentialityProfile := [mandarin, japanese, korean]

theorem east_asian_no_evidentials :
    eastAsian.all (·.system == .noGrammatical) = true := by
  native_decide

/-- Americas languages in our sample (Quechua, Aymara, Tuyuca, Kashaya,
    Tariana) all have three-or-more evidential categories. The Americas
    have the highest density of complex evidential systems worldwide. -/
def americas : List EvidentialityProfile :=
  [quechua, aymara, tuyuca, kashaya, tariana]

theorem americas_all_complex_evidentials :
    americas.all (·.system == .threeOrMore) = true := by
  native_decide

/-- All Americas languages in our sample use verbal affixes. -/
theorem americas_all_verbal_affix :
    americas.all (·.coding == .verbalAffix) = true := by
  native_decide

end Phenomena.Modality.Typology
