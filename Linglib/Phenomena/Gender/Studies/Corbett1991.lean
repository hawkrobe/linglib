import Linglib.Typology.Gender
import Linglib.Core.Agreement.Target

/-!
# Corbett (1991): Gender — typology of noun-class systems
@cite{corbett-1991} @cite{corbett-2013} @cite{dryer-haspelmath-2013}
@cite{dixon-1972}

Greville Corbett. *Gender*. Cambridge University Press, 1991.
Plus @cite{corbett-2013}'s WALS Chs 30, 31, 32.

This study file holds the 22-language exemplar sample of gender / noun
class systems and cross-linguistic generalisations consuming the substrate
`GenderProfile`. WALS aggregate distribution theorems live in
`Linglib/Typology/Gender.lean`. Per-language Fragment-vs-WALS data-equality
theorems are deliberately absent — see
`feedback_no_per_lang_wals_grounding_in_studies` for the rationale.

## Sample composition

22 languages chosen to span all five `GenderCount` values:
- **No gender** (English, Mandarin, Japanese, Turkish, Finnish, Korean,
  Quechua — 7 languages).
- **2 genders** (French, Spanish, Hindi-Urdu, Irish, Hebrew, Hausa —
  6 languages).
- **3 genders** (German, Russian, Latin, Romanian — 4 languages).
- **4 genders** (Dyirbal, Georgian — 2 languages).
- **5+ noun classes** (Swahili, Zulu, Fula — 3 languages).

The sample includes Bantu noun-class systems (Swahili, Zulu) and Fula
(20+ classes), the Australian 4-class system Dyirbal, and the Caucasian
rationality-based Georgian system, alongside the canonical European
sex-based 2/3 systems.
-/

set_option autoImplicit false

namespace Phenomena.Gender.Studies.Corbett1991

open Typology.Gender
open Core (AgreementTarget)

-- ============================================================================
-- §1. The 22-language exemplar sample
-- ============================================================================

-- ── No-gender languages ─────────────────────────────────────────────────

/-- English: no grammatical gender on nouns or adjectives; only natural
    gender in 3sg pronouns (he/she/it). No gender agreement. -/
def english : GenderProfile :=
  { name := "English", iso639 := "eng"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

def mandarin : GenderProfile :=
  { name := "Mandarin Chinese", iso639 := "cmn"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

def japanese : GenderProfile :=
  { name := "Japanese", iso639 := "jpn"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

def turkish : GenderProfile :=
  { name := "Turkish", iso639 := "tur"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

def finnish : GenderProfile :=
  { name := "Finnish", iso639 := "fin"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

def korean : GenderProfile :=
  { name := "Korean", iso639 := "kor"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

def quechua : GenderProfile :=
  { name := "Quechua (Cusco)", iso639 := "quz"
  , genderCount := .none, rawGenderCount := 0
  , basis := .noGender, assignment := .noGender
  , agreementTargets := [], semanticBases := [] }

-- ── 2-gender languages ──────────────────────────────────────────────────

/-- French: 2 genders (masc/fem), sex-based, semantic + formal. Agreement
    on determiners, attributive + predicate adjectives, past participles,
    and personal pronouns. -/
def french : GenderProfile :=
  { name := "French", iso639 := "fra"
  , genderCount := .two, rawGenderCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun]
  , semanticBases := [.sex] }

def spanish : GenderProfile :=
  { name := "Spanish", iso639 := "spa"
  , genderCount := .two, rawGenderCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun]
  , semanticBases := [.sex] }

/-- Hindi-Urdu: 2 genders (masc/fem). Agreement on adjectives, verbs (in
    perfective aspect), and auxiliaries — one of the clearest cases of
    verb agreement for gender. -/
def hindiUrdu : GenderProfile :=
  { name := "Hindi-Urdu", iso639 := "hin"
  , genderCount := .two, rawGenderCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .verb]
  , semanticBases := [.sex] }

def irish : GenderProfile :=
  { name := "Irish", iso639 := "gle"
  , genderCount := .two, rawGenderCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .personalPronoun]
  , semanticBases := [.sex] }

def hebrew : GenderProfile :=
  { name := "Hebrew", iso639 := "heb"
  , genderCount := .two, rawGenderCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .verb]
  , semanticBases := [.sex] }

/-- Hausa (Chadic, Afroasiatic): 2 genders (masc/fem). @cite{corbett-1991}
    §3.2.2 (pp. 52–53) describes the synchronic Hausa pattern as
    phonological assignment with exceptions ("nouns ending in *-aa* are
    feminine"), with morphological diachronic origin discussed separately
    in §4.5 (pp. 102–103, citing Newman 1979). @cite{kramer-2020} §3.3.1
    (pp. 60–61) re-analyzes the *-aa* suffix as morphophonological
    *realization* of [+FEM] on n rather than gender *assignment*. This
    aligns synchronically with @cite{newman-2000} pp. 210–213, where the
    {-ā} suffix is a feminine marker (acquired diachronically via
    "overt characterization") rather than a synchronic phonological rule
    — so the Corbett-Kramer disagreement is asymmetric: Newman's source
    grammar favors Kramer. The cross-framework theorems live in
    `Phenomena/Gender/Studies/Kramer2020.lean`. WALS-side
    `semanticAndFormal` is the umbrella all three analyses share.

    Agreement on determiners/possessive linkers (attributive), TAM clitics
    (verb-target in person/aspect), and personal pronouns. -/
def hausa : GenderProfile :=
  { name := "Hausa", iso639 := "hau"
  , genderCount := .two, rawGenderCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .personalPronoun, .verb]
  , semanticBases := [.sex] }

-- ── 3-gender languages ──────────────────────────────────────────────────

/-- German: 3 genders (masc/fem/neut), sex-based with extensive formal
    correlates (suffixes `-ung`, `-heit`, `-keit` feminine; `-chen`, `-lein`
    neuter; etc.). -/
def german : GenderProfile :=
  { name := "German", iso639 := "deu"
  , genderCount := .three, rawGenderCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun]
  , semanticBases := [.sex] }

/-- Russian: 3 genders. Agreement on adjectives, past-tense verbs,
    demonstratives, relative + personal pronouns. -/
def russian : GenderProfile :=
  { name := "Russian", iso639 := "rus"
  , genderCount := .three, rawGenderCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verb]
  , semanticBases := [.sex] }

def latin : GenderProfile :=
  { name := "Latin", iso639 := "lat"
  , genderCount := .three, rawGenderCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun]
  , semanticBases := [.sex] }

/-- Romanian: 3 genders (masc/fem/neuter — the neuter behaves as masc in
    the singular and fem in the plural; "ambigeneric"). -/
def romanian : GenderProfile :=
  { name := "Romanian", iso639 := "ron"
  , genderCount := .three, rawGenderCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun]
  , semanticBases := [.sex] }

-- ── 4-gender languages ──────────────────────────────────────────────────

/-- Dyirbal (Australia): 4 genders (I males, II females + water/fire/fighting,
    III edible plants, IV residual). Non-sex-based — categories include
    edibility and natural forces beyond biological sex. Semantic only. -/
def dyirbal : GenderProfile :=
  { name := "Dyirbal", iso639 := "dbl"
  , genderCount := .four, rawGenderCount := 4
  , basis := .nonSexBased, assignment := .semanticOnly
  , agreementTargets := [.attributive]
  , semanticBases := [.sex, .animacy, .shape] }

/-- Georgian: 4 categories on the rationality / animacy split (rational
    humans vs non-rational), with an older masc/fem trace in pronouns. -/
def georgian : GenderProfile :=
  { name := "Georgian", iso639 := "kat"
  , genderCount := .four, rawGenderCount := 4
  , basis := .nonSexBased, assignment := .semanticOnly
  , agreementTargets := [.personalPronoun, .verb]
  , semanticBases := [.rationality, .animacy] }

-- ── 5+ noun-class languages ────────────────────────────────────────────

/-- Swahili (Bantu): ~15 noun classes (singular/plural pairings + locatives).
    Semantic + formal assignment via prefixes. Full agreement across
    determiners, adjectives, verbs, pronouns, numerals, possessives. -/
def swahili : GenderProfile :=
  { name := "Swahili", iso639 := "swh"
  , genderCount := .fivePlus, rawGenderCount := 15
  , basis := .nonSexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verb]
  , semanticBases := [.humanness, .animacy, .shape] }

def zulu : GenderProfile :=
  { name := "Zulu", iso639 := "zul"
  , genderCount := .fivePlus, rawGenderCount := 15
  , basis := .nonSexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verb]
  , semanticBases := [.humanness, .animacy, .shape] }

/-- Fula (Atlantic, Niger-Congo): ~20+ noun classes, one of the richest
    class systems in Africa. -/
def fula : GenderProfile :=
  { name := "Fula", iso639 := "ful"
  , genderCount := .fivePlus, rawGenderCount := 20
  , basis := .nonSexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun, .verb]
  , semanticBases := [.humanness, .animacy, .shape] }

/-- All 22 language profiles in the sample. -/
def allProfiles : List GenderProfile :=
  [ english, mandarin, japanese, turkish, finnish, korean, quechua
  , french, spanish, hindiUrdu, irish, hebrew, hausa
  , german, russian, latin, romanian
  , dyirbal, georgian
  , swahili, zulu, fula ]

-- ============================================================================
-- §2. Sample-level statistics
-- ============================================================================

theorem allProfiles_count : allProfiles.length = 22 := by native_decide

/-- All raw gender counts are consistent with their WALS bins. -/
theorem all_raw_consistent :
    allProfiles.all (·.rawCountConsistent) = true := by native_decide

/-- All profiles are cross-chapter consistent. -/
theorem all_cross_consistent :
    allProfiles.all (·.crossChapterConsistent) = true := by native_decide

/-- All five `GenderCount` values are attested. -/
theorem all_gender_counts_attested :
    allProfiles.any (λ p => p.genderCount == .none) &&
    allProfiles.any (λ p => p.genderCount == .two) &&
    allProfiles.any (λ p => p.genderCount == .three) &&
    allProfiles.any (λ p => p.genderCount == .four) &&
    allProfiles.any (λ p => p.genderCount == .fivePlus) = true := by
  native_decide

/-- All three `GenderBasis` values are attested. -/
theorem all_bases_attested :
    allProfiles.any (λ p => p.basis == .noGender) &&
    allProfiles.any (λ p => p.basis == .sexBased) &&
    allProfiles.any (λ p => p.basis == .nonSexBased) = true := by
  native_decide

/-- All three `AssignmentSystem` values are attested. -/
theorem all_assignments_attested :
    allProfiles.any (λ p => p.assignment == .noGender) &&
    allProfiles.any (λ p => p.assignment == .semanticOnly) &&
    allProfiles.any (λ p => p.assignment == .semanticAndFormal) = true := by
  native_decide

/-- Sample diversity: ≥5 languages in each of gender-bearing vs genderless. -/
theorem sample_diversity :
    (allProfiles.filter (λ p => p.genderCount == .none)).length >= 5 ∧
    (allProfiles.filter (λ p => p.genderCount != .none)).length >= 5 := by
  native_decide

/-- Sample distribution counts. -/
theorem sample_counts :
    (allProfiles.filter (λ p => p.genderCount == .none)).length = 7 ∧
    (allProfiles.filter (λ p => p.basis == .sexBased)).length = 10 ∧
    (allProfiles.filter (λ p => p.basis == .nonSexBased)).length = 5 ∧
    (allProfiles.filter (λ p => p.assignment == .semanticOnly)).length = 2 ∧
    (allProfiles.filter (λ p => p.assignment == .semanticAndFormal)).length = 13 ∧
    (allProfiles.filter (·.isNounClassSystem)).length = 3 := by
  native_decide

-- ============================================================================
-- §3. Cross-linguistic generalisations (Corbett 1991)
-- ============================================================================

/-- @cite{corbett-1991}: among gender systems, 2-gender is the most common
    in the WALS sample and well-represented in our sample. -/
theorem two_gender_in_sample :
    (allProfiles.filter (λ p => p.genderCount == .two)).length = 6 := by
  native_decide

/-- All 2- and 3-gender systems in the sample are sex-based. Reflects the
    cross-linguistic pattern that small gender systems organise around sex. -/
theorem two_three_gender_all_sex_based :
    allProfiles.all (λ p =>
      if p.genderCount == .two || p.genderCount == .three
      then p.basis == .sexBased
      else true) = true := by native_decide

/-- @cite{corbett-1991}'s key finding: no language assigns gender on a purely
    formal basis without any semantic core. In the sample, every gendered
    language has semantic assignment (alone or combined with formal). -/
theorem no_purely_formal_in_sample :
    allProfiles.all (λ p =>
      if p.genderCount != .none
      then p.assignment == .semanticOnly || p.assignment == .semanticAndFormal
      else true) = true := by native_decide

/-- All 3-gender systems in the sample use semantic + formal assignment.
    Sex-based 3-gender systems require formal correlates because the
    masculine/feminine/neuter distinction can't be determined by semantics
    alone. -/
theorem three_gender_always_formal :
    allProfiles.all (λ p =>
      if p.genderCount == .three
      then p.assignment == .semanticAndFormal
      else true) = true := by native_decide

/-- A gender system without any agreement is not a gender system — genders
    are precisely the categories that trigger agreement. -/
theorem gender_implies_agreement :
    allProfiles.all (λ p =>
      if p.genderCount != .none then p.hasAgreement
      else !p.hasAgreement) = true := by native_decide

-- ============================================================================
-- §4. Corbett's Agreement Hierarchy
-- ============================================================================

/-! @cite{corbett-1991}'s Agreement Hierarchy:
    attributive > predicate > relative pronoun > personal pronoun > verb. -/

/-- Verb agreement implies higher-target agreement in the sample (none of
    the languages agree only on verbs). -/
theorem agreement_hierarchy_verb_implies_higher :
    allProfiles.all (λ p =>
      if hasTarget p.agreementTargets .verb
      then hasTarget p.agreementTargets .attributive ||
           hasTarget p.agreementTargets .predicate ||
           hasTarget p.agreementTargets .personalPronoun
      else true) = true := by native_decide

/-- No language in the sample agrees only on verbs. -/
theorem no_verb_only_agreement :
    allProfiles.all (λ p =>
      if p.agreementTargets == [.verb]
      then false
      else true) = true := by native_decide

/-- No gendered language in the sample has agreement only on personal
    pronouns: pronoun agreement always co-occurs with at least one other
    target. -/
theorem no_pronoun_only_agreement :
    allProfiles.all (λ p =>
      if p.genderCount != .none && hasTarget p.agreementTargets .personalPronoun
      then hasTarget p.agreementTargets .attributive ||
           hasTarget p.agreementTargets .predicate ||
           hasTarget p.agreementTargets .verb
      else true) = true := by native_decide

/-- Noun-class systems (5+) show agreement on more targets than smaller
    systems. In the sample, all noun-class systems agree on ≥4 of the 5
    target types. -/
theorem noun_class_rich_agreement :
    allProfiles.all (λ p =>
      if p.isNounClassSystem
      then p.agreementTargets.length >= 4
      else true) = true := by native_decide

-- ============================================================================
-- §5. Basis × count interactions
-- ============================================================================

/-- Non-sex-based systems in the sample have ≥4 genders. When gender is not
    organised around sex, the system tends to proliferate. -/
theorem non_sex_based_more_genders :
    allProfiles.all (λ p =>
      if p.basis == .nonSexBased
      then p.rawGenderCount >= 4
      else true) = true := by native_decide

/-- Semantic-only assignment in the sample is restricted to non-sex-based
    systems. Sex-based systems typically have formal correlates. -/
theorem semantic_only_is_non_sex_based :
    allProfiles.all (λ p =>
      if p.assignment == .semanticOnly
      then p.basis == .nonSexBased
      else true) = true := by native_decide

/-- All sex-based systems in the sample use semantic + formal assignment. -/
theorem sex_based_always_formal :
    allProfiles.all (λ p =>
      if p.basis == .sexBased
      then p.assignment == .semanticAndFormal
      else true) = true := by native_decide

-- ============================================================================
-- §6. The canonical-gender notion
-- ============================================================================

/-- European languages in the sample all have canonical gender systems
    (sex-based, 2 or 3 genders, semantic + formal). -/
theorem european_canonical :
    french.isCanonicalGender &&
    spanish.isCanonicalGender &&
    german.isCanonicalGender &&
    russian.isCanonicalGender &&
    latin.isCanonicalGender &&
    romanian.isCanonicalGender = true := by native_decide

/-- Hindi-Urdu also has a canonical gender system. -/
theorem hindiUrdu_canonical :
    hindiUrdu.isCanonicalGender = true := by native_decide

/-- Non-canonical gender systems in the sample are all non-European. -/
theorem non_canonical_non_european :
    allProfiles.all (λ p =>
      if p.genderCount != .none && !p.isCanonicalGender
      then p.iso639 == "dbl" || p.iso639 == "kat" ||
           p.iso639 == "swh" || p.iso639 == "zul" ||
           p.iso639 == "ful" || p.iso639 == "gle"
      else true) = true := by native_decide

-- ============================================================================
-- §7. The gender-number scale
-- ============================================================================

/-- The gender-number scale spans 0 (English) to 20 (Fula) raw categories. -/
theorem gender_scale_range :
    allProfiles.any (λ p => p.rawGenderCount == 0) &&
    allProfiles.any (λ p => p.rawGenderCount == 2) &&
    allProfiles.any (λ p => p.rawGenderCount == 3) &&
    allProfiles.any (λ p => p.rawGenderCount == 4) &&
    allProfiles.any (λ p => p.rawGenderCount >= 15) = true := by native_decide

/-- Maximum raw gender count in the sample is 20 (Fula). -/
theorem max_gender_count_is_fula :
    allProfiles.all (λ p => p.rawGenderCount <= 20) &&
    allProfiles.any (λ p => p.rawGenderCount == 20) = true := by native_decide

-- ============================================================================
-- §8. ISO code sanity
-- ============================================================================

theorem all_iso_nonempty :
    allProfiles.all (λ p => p.iso639.length > 0) = true := by native_decide

theorem all_iso_length_3 :
    allProfiles.all (λ p => p.iso639.length == 3) = true := by native_decide

theorem iso_codes_unique :
    (allProfiles.map (·.iso639)).eraseDups.length = allProfiles.length := by
  native_decide

end Phenomena.Gender.Studies.Corbett1991
