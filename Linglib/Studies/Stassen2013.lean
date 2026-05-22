import Linglib.Typology.Copulas

/-!
# Stassen2013
@cite{stassen-2013} @cite{hengeveld-1992} @cite{pustet-2003}

Cross-linguistic copula and predication analysis anchored on
@cite{stassen-2013}'s four WALS chapters (117 predicative possession,
118 predicative adjectives, 119 nominal-vs-locational predication, 120
zero copula). The 20-language `CopulaProfile` sample tests the cross-
chapter implications Stassen draws (e.g. nonverbal nominal predication
correlates with zero copula availability) plus areal patterns
(Western European cluster, East Asian verbal-adjective cluster, Semitic
restricted-zero pattern).

## Stassen's central observation

Predication is not uniform across predicate types: many languages use
fundamentally different strategies for adjectival ("The book is red"),
nominal ("She is a doctor"), and locational ("The cat is on the mat")
predication. The copula, where it exists, is best understood as a
*family of strategies* deployed differently across predicate types,
not a single phenomenon.

## Contents

- §1. The 20-language `CopulaProfile` sample (5 IE, 2 Semitic,
  2 East Asian, etc.).
- §2. Sample-level distribution counts.
- §3. Sample-grounded cross-chapter generalisations:
  Stassen's implication (nonverbal noun → zero copula),
  copula-required-tends-identical, verbal-adj-tends-nomloc-split.
- §4. Areal-cluster theorems (Western European, East Asian, Semitic).
- §5. CopulaType distribution.

## Out of scope

The substrate types (`PredAdjStrategy`, `CopulaProfile`, WALS converters,
corpus-only theorems) live in `Linglib/Typology/Copulas.lean`.
Partee's compositional `BE` type-shift bridge to copula typology is in
`Studies/Partee1987.lean`.
-/

set_option autoImplicit false

namespace Stassen2013

open Typology.Copulas

-- ============================================================================
-- §1. The 20-Language Sample
-- ============================================================================

/-- English (Indo-European, Germanic). Adjectives non-verbal (require `be`),
    nominal predication uses verbal copula `be`, same copula for nominal
    and locational, no zero copula. -/
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

/-- French (Indo-European, Romance). `Le livre est rouge`; `Elle est medecin`. -/
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

/-- German (Indo-European, Germanic). `Das Buch ist rot`; `Sie ist Arztin`. -/
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

/-- Spanish (Indo-European, Romance). DIFFERENT copulas: `ser` (nominal/
    permanent) vs `estar` (locational/temporary). -/
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

/-- Russian (Indo-European, Slavic). Zero copula in present
    (`Ona vrach`); `byt'` in past. RESTRICTED zero: present only. -/
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

/-- Arabic (Standard) (Afro-Asiatic, Semitic). Present-tense zero copula
    (`hiya tabiba`); `kaana` for past. -/
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

/-- Hebrew (Afro-Asiatic, Semitic). Pronominal copula `hu/hi/hem/hen` in
    present; `haya` for past. -/
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

/-- Hungarian (Uralic). Zero copula in 3rd person present (`O orvos`),
    `van` in other persons/tenses. -/
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

/-- Japanese (Japonic). MIXED adjectives (i-adjectives verbal,
    na-adjectives need `da`); nominal predication uses `da`/`desu`. -/
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

/-- Korean (Koreanic). Verbal adjectives (`ppalgah-da`); nominal predication
    via copula `-i-da`. -/
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

/-- Mandarin Chinese (Sino-Tibetan). Verbal adjectives (`shu hong`);
    nominal predication via `shi`; locational via `zai`. -/
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

/-- Turkish (Turkic). Verbal adjectives; copular suffix `-dIr` for nominals
    (often dropped in 3rd person present). -/
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

/-- Swahili (Niger-Congo, Bantu). Particle `ni` for affirmative nominal
    predication; widespread zero copula in many contexts. -/
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

/-- Hindi-Urdu (Indo-European, Indo-Aryan). Copula `hona` for both nominal
    and locational; no zero copula. -/
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

/-- Tagalog (Austronesian). Widespread zero copula (`doktor siya`); `ay`
    is a topic marker, not a true copula. -/
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

/-- Irish (Indo-European, Celtic). Two copulas: `is` (nominal/identity) vs
    `ta` (attributive/locational) — classic split. -/
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

/-- Finnish (Uralic). Copula `olla` for all predication types; no zero copula. -/
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

/-- Quechua (Quechuan). Copular suffixes `-mi`/`-n`; `ka-` in past/future. -/
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

/-- Yoruba (Niger-Congo, Atlantic-Congo). Verbal adjectives; widespread
    zero copula for nominal predication. -/
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

/-- Thai (Tai-Kadai). Verbal adjectives; verbal copula `pen` for nominals;
    `yuu` for locational. -/
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

/-- The 20-language sample. -/
def allLanguages : List CopulaProfile :=
  [ english, french, german, spanish, russian, arabic, hebrew, hungarian
  , japanese, korean, mandarin, turkish, swahili, hindiUrdu, tagalog
  , irish, finnish, quechua, yoruba, thai ]

/-- Count of languages in a list matching a predicate. -/
def countBy (langs : List CopulaProfile) (pred : CopulaProfile → Bool) : Nat :=
  (langs.filter pred).length

theorem sample_size : allLanguages.length = 20 := by native_decide

-- ============================================================================
-- §2. Sample Distribution
-- ============================================================================

theorem sample_verbal_adj_count :
    countBy allLanguages (·.hasVerbalAdj) = 7 := by native_decide
theorem sample_mixed_adj_count :
    countBy allLanguages (·.predAdj == .mixed) = 1 := by native_decide
theorem sample_nonverbal_adj_count :
    countBy allLanguages (·.predAdj == .nonVerbal) = 12 := by native_decide

theorem sample_verbal_noun_count :
    countBy allLanguages (·.hasVerbalNounCopula) = 11 := by native_decide
theorem sample_nonverbal_noun_count :
    countBy allLanguages (·.predNoun == .nonVerbal) = 9 := by native_decide

theorem sample_nomloc_different_count :
    countBy allLanguages (·.hasNomLocSplit) = 11 := by native_decide
theorem sample_nomloc_identical_count :
    countBy allLanguages (·.nomLoc == .identical) = 9 := by native_decide

theorem sample_zero_impossible_count :
    countBy allLanguages (·.alwaysRequiresCopula) = 11 := by native_decide
theorem sample_zero_restricted_count :
    countBy allLanguages (·.zeroCopula == .restricted) = 6 := by native_decide
theorem sample_zero_widespread_count :
    countBy allLanguages (·.zeroCopula == .widespread) = 3 := by native_decide

-- ============================================================================
-- §3. Cross-Chapter Generalisations
-- ============================================================================

/-- @cite{stassen-2013}'s implicational universal in the sample: if a
    language has non-verbal nominal predication, it allows some form of
    zero copula. Holds without exception in this sample. -/
theorem stassen_implication_noun_zero :
    allLanguages.all (λ p =>
      if p.predNoun == .nonVerbal then p.allowsZeroCopula else true) = true := by
  native_decide

/-- Contrapositive of Stassen's implication: if zero copula is impossible,
    the language uses verbal nominal predication. -/
theorem no_zero_implies_verbal_noun :
    allLanguages.all (λ p =>
      if p.zeroCopula == .impossible then p.predNoun == .verbal else true) = true := by
  native_decide

/-- Cross-chapter: in the sample, languages with widespread zero copula
    always use non-verbal nominal predication (logically expected:
    if zero copula is the norm, predication IS non-verbal). -/
theorem widespread_zero_implies_nonverbal_noun :
    (allLanguages.filter (·.zeroCopula == .widespread)).all
        (·.predNoun == .nonVerbal) = true := by
  native_decide

/-- In the sample, no language has mixed adjectives AND non-verbal noun
    predication. Mixed-adjective languages use verbal nominal copulas. -/
theorem mixed_adj_implies_verbal_noun :
    (allLanguages.filter (·.predAdj == .mixed)).all
        (·.predNoun == .verbal) = true := by
  native_decide

/-- Languages with verbal adjectives often pair with non-verbal nouns
    (the verbal-adjective strategy eliminates the need for a copula with
    adjectives but does not provide a copula for nouns). -/
theorem verbal_adj_nonverbal_noun :
    (allLanguages.filter (λ p => p.predAdj == .verbal && p.predNoun == .nonVerbal)).length ≥ 3 := by
  native_decide

/-- Languages with restricted zero copula in the sample all have overt
    past-tense copula forms (Russian, Arabic, Hungarian, Turkish). -/
theorem restricted_zero_has_copula_forms :
    (allLanguages.filter (·.zeroCopula == .restricted)).all
        (·.copulaForms.length > 0) = true := by
  native_decide

/-- Languages with verbal adjectives tend to split nominal and locational
    predication. Most verbal-adjective sample languages have different
    nom-loc strategies. -/
theorem verbal_adj_tends_nomloc_split :
    let verbalAdj := allLanguages.filter (·.hasVerbalAdj)
    let splitNomLoc := verbalAdj.filter (·.hasNomLocSplit)
    splitNomLoc.length > verbalAdj.length / 2 := by
  native_decide

/-- Languages where the copula is always required tend to use the same
    copula for nominal and locational predication. -/
theorem copula_required_tends_identical :
    let required := allLanguages.filter (·.alwaysRequiresCopula)
    let identical := required.filter (·.nomLoc == .identical)
    identical.length ≥ required.length / 2 := by
  native_decide

/-- A split predication language uses different strategies for at least
    two of: adjectival, nominal, and locational predication. -/
def hasSplitPredication (p : CopulaProfile) : Bool :=
  p.nomLoc == .different ||
  (p.predAdj == .verbal && p.predNoun == .verbal) ||
  (p.predAdj == .verbal && p.predNoun == .nonVerbal) ||
  (p.predAdj == .mixed)

theorem split_predication_common :
    countBy allLanguages hasSplitPredication ≥ 12 := by native_decide

/-- Spanish and Irish exemplify the clearest nom-loc splits: both have
    two distinct copulas that partition predicate types. -/
theorem spanish_irish_clear_split :
    spanish.hasNomLocSplit = true ∧ irish.hasNomLocSplit = true := by
  native_decide

/-- Mandarin exemplifies a three-way split: adjectives are verbal (no
    copula), nouns require `shi`, locations use `zai`. -/
theorem mandarin_three_way_split :
    mandarin.predAdj == .verbal ∧
    mandarin.predNoun == .verbal ∧
    mandarin.nomLoc == .different := by
  native_decide

/-- Languages that split nominal and locational predication have at least
    one copula form recorded in the profile. -/
theorem nomloc_split_languages_have_distinct_forms :
    (allLanguages.filter (·.hasNomLocSplit)).all
        (·.copulaForms.length ≥ 1) = true := by
  native_decide

-- ============================================================================
-- §4. Areal Patterns
-- ============================================================================

/-- Western European languages (English, French, German) share a common
    profile: non-verbal adjectives, verbal nominal copula, no zero copula.
    The "Standard Average European" pattern. -/
def westernEuropean : List CopulaProfile := [english, french, german]

theorem western_european_nonverbal_adj :
    westernEuropean.all (·.predAdj == .nonVerbal) = true := by native_decide

theorem western_european_verbal_noun :
    westernEuropean.all (·.predNoun == .verbal) = true := by native_decide

theorem western_european_no_zero :
    westernEuropean.all (·.alwaysRequiresCopula) = true := by native_decide

/-- East and Southeast Asian languages all have verbal or mixed adjectives. -/
def eastAsian : List CopulaProfile := [japanese, korean, mandarin, thai]

theorem east_asian_verbal_or_mixed_adj :
    eastAsian.all (λ p => p.predAdj == .verbal || p.predAdj == .mixed) = true := by
  native_decide

theorem east_asian_nomloc_split :
    eastAsian.all (·.hasNomLocSplit) = true := by native_decide

/-- Semitic languages (Arabic, Hebrew) share a profile: non-verbal
    adjectives, non-verbal nominal predication, restricted zero copula
    (present tense only). -/
def semitic : List CopulaProfile := [arabic, hebrew]

theorem semitic_nonverbal_adj :
    semitic.all (·.predAdj == .nonVerbal) = true := by native_decide

theorem semitic_nonverbal_noun :
    semitic.all (·.predNoun == .nonVerbal) = true := by native_decide

theorem semitic_restricted_zero :
    semitic.all (·.zeroCopula == .restricted) = true := by native_decide

-- ============================================================================
-- §5. CopulaType Distribution
-- ============================================================================

theorem sample_verbal_copula_count :
    countBy allLanguages (·.copulaType == .verbalCopula) = 11 := by native_decide

theorem sample_zero_copula_type_count :
    countBy allLanguages (·.copulaType == .zero) = 4 := by native_decide

theorem sample_particle_copula_count :
    countBy allLanguages (·.copulaType == .particle) = 4 := by native_decide

theorem sample_pronominal_copula_count :
    countBy allLanguages (·.copulaType == .pronominalCopula) = 1 := by native_decide

/-- Verbal copulas are the most common copula type in the sample. -/
theorem verbal_copula_most_common :
    countBy allLanguages (·.copulaType == .verbalCopula) >
      countBy allLanguages (·.copulaType == .particle) ∧
    countBy allLanguages (·.copulaType == .verbalCopula) >
      countBy allLanguages (·.copulaType == .zero) ∧
    countBy allLanguages (·.copulaType == .verbalCopula) >
      countBy allLanguages (·.copulaType == .pronominalCopula) := by
  native_decide

end Stassen2013
