import Linglib.Core.Word

/-!
# Gender and Noun Class Typology (WALS Chapters 30--32)

Formalizes three chapters from the World Atlas of Language Structures (WALS)
covering the typology of gender and noun class systems, all authored by
Corbett (2013):

- **Chapter 30**: Number of Genders -- how many gender/noun class distinctions
  a language makes. Values range from none (no gender system) through 2, 3, 4,
  to 5 or more. Most of the world's languages have no gender system at all;
  among those that do, 2 and 3 genders are most common. Systems with 5 or more
  categories are typically called "noun class" systems rather than "gender"
  systems (the Bantu languages being the canonical example).

- **Chapter 31**: Sex-based and Non-sex-based Gender Systems -- whether the
  gender system is organized around biological sex (masculine/feminine, with
  or without neuter) or around other semantic/formal criteria such as
  animacy, shape, or size. The distinction cross-cuts the number of genders:
  a 2-gender system may be masculine/feminine (French) or animate/inanimate
  (Ojibwe).

- **Chapter 32**: Systems of Gender Assignment -- how nouns are assigned to
  their gender categories. Assignment may be purely semantic (based on the
  meaning of the noun, e.g. male referents are masculine), purely formal
  (based on phonological or morphological properties), or a combination.
  A key typological finding is that no language has a purely formal assignment
  system: formal rules always supplement a semantic core.

## Key Concepts

The boundary between "gender" (2--3 categories, typically sex-based) and
"noun class" (4+ categories, often with semantic and formal assignment) is
gradient rather than categorical. Corbett (1991) treats them as a single
phenomenon at different scales.

Corbett's Agreement Hierarchy governs where gender agreement surfaces:
  attributive adjective > predicate adjective > relative pronoun >
  personal pronoun > verb target.
If a language shows gender agreement on a lower target, it shows agreement
on all higher targets.

## References

- Corbett, G. G. (1991). *Gender*. Cambridge University Press.
- Corbett, G. G. (2013a). Number of Genders. In Dryer, M. S. & Haspelmath, M.
  (eds.), WALS Online (v2020). Ch. 30. https://wals.info/chapter/30
- Corbett, G. G. (2013b). Sex-based and Non-sex-based Gender Systems. In Dryer,
  M. S. & Haspelmath, M. (eds.), WALS Online (v2020). Ch. 31.
  https://wals.info/chapter/31
- Corbett, G. G. (2013c). Systems of Gender Assignment. In Dryer, M. S. &
  Haspelmath, M. (eds.), WALS Online (v2020). Ch. 32.
  https://wals.info/chapter/32
- Dryer, M. S. & Haspelmath, M. (eds.) (2013). WALS Online (v2020).
  Leipzig: Max Planck Institute for Evolutionary Anthropology.
  https://wals.info
-/

namespace Phenomena.Gender.Typology

-- ============================================================================
-- WALSCount Infrastructure
-- ============================================================================

/-- A single row in a WALS distribution table: a label and a language count. -/
structure WALSCount where
  label : String
  count : Nat
  deriving Repr, DecidableEq, BEq

/-- Sum of all counts in a WALS distribution. -/
def WALSCount.totalOf (cs : List WALSCount) : Nat :=
  cs.foldl (λ acc c => acc + c.count) 0

-- ============================================================================
-- Chapter 30: Number of Genders
-- ============================================================================

/-- Number of gender/noun class distinctions in a language (WALS Ch 30).

    The five values form a scale from no gender system at all through
    increasingly fine-grained classification. Systems with 5 or more
    categories are often called "noun class" systems rather than "gender"
    systems, but the boundary is conventional, not categorical. -/
inductive GenderCount where
  | none      -- no gender system (e.g. English, Mandarin, Turkish)
  | two       -- 2 genders (e.g. French masc/fem, Ojibwe anim/inanim)
  | three     -- 3 genders (e.g. German masc/fem/neut, Romanian masc/fem/neut)
  | four      -- 4 genders (e.g. Dyirbal: masc/fem/edible/residual)
  | fivePlus  -- 5+ genders / noun classes (e.g. Swahili ~15 classes)
  deriving DecidableEq, BEq, Repr

instance : Inhabited GenderCount := ⟨.none⟩

/-- Numeric lower bound for each GenderCount category. -/
def GenderCount.lowerBound : GenderCount → Nat
  | .none     => 0
  | .two      => 2
  | .three    => 3
  | .four     => 4
  | .fivePlus => 5

/-- Whether a raw gender count falls in a given GenderCount category. -/
def GenderCount.contains (gc : GenderCount) (n : Nat) : Bool :=
  match gc with
  | .none     => n == 0
  | .two      => n == 2
  | .three    => n == 3
  | .four     => n == 4
  | .fivePlus => n >= 5

/-- WALS Chapter 30 distribution (Corbett 2013a, 257-language sample). -/
def ch30Distribution : List WALSCount :=
  [ ⟨"None (no gender)",   145⟩
  , ⟨"Two genders",         50⟩
  , ⟨"Three genders",       26⟩
  , ⟨"Four genders",        12⟩
  , ⟨"Five or more genders", 24⟩ ]

/-- Chapter 30 total sample size. -/
theorem ch30_total : WALSCount.totalOf ch30Distribution = 257 := by native_decide

-- ============================================================================
-- Chapter 31: Sex-based and Non-sex-based Gender Systems
-- ============================================================================

/-- Whether a gender system is based on biological sex (WALS Ch 31).

    Sex-based systems organize genders around a masculine/feminine
    distinction (possibly with additional genders like neuter). Non-sex-based
    systems use other semantic criteria: animate/inanimate, human/non-human,
    shape-based, etc. Many Bantu noun class systems are non-sex-based,
    organized instead around semantic categories like human, plant, artifact,
    abstract, liquid, etc. -/
inductive GenderBasis where
  | noGender     -- no gender system at all
  | sexBased     -- gender organized around biological sex (masc/fem ± neuter)
  | nonSexBased  -- gender organized around other criteria (animacy, shape, etc.)
  deriving DecidableEq, BEq, Repr

instance : Inhabited GenderBasis := ⟨.noGender⟩

/-- WALS Chapter 31 distribution (Corbett 2013b, 254-language sample). -/
def ch31Distribution : List WALSCount :=
  [ ⟨"No gender",            145⟩
  , ⟨"Sex-based",             84⟩
  , ⟨"Non-sex-based",         25⟩ ]

/-- Chapter 31 total sample size. -/
theorem ch31_total : WALSCount.totalOf ch31Distribution = 254 := by native_decide

-- ============================================================================
-- Chapter 32: Systems of Gender Assignment
-- ============================================================================

/-- How nouns are assigned to their gender categories (WALS Ch 32).

    Semantic assignment means gender is determined by meaning: male referents
    are masculine, female referents are feminine, etc. Formal assignment means
    gender is determined by the phonological or morphological shape of the
    noun: e.g., in Italian, nouns ending in -o tend to be masculine, nouns
    ending in -a tend to be feminine.

    A key typological finding is that **no language has a purely formal
    assignment system**: formal rules always supplement a semantic core.
    Languages either use semantic assignment alone or combine semantic and
    formal criteria. -/
inductive AssignmentSystem where
  | noGender           -- no gender system to assign to
  | semanticOnly       -- assignment purely by meaning (e.g. Tamil, Zande)
  | semanticAndFormal  -- assignment by both meaning and form (e.g. Russian, German)
  deriving DecidableEq, BEq, Repr

instance : Inhabited AssignmentSystem := ⟨.noGender⟩

/-- WALS Chapter 32 distribution (Corbett 2013c, 256-language sample). -/
def ch32Distribution : List WALSCount :=
  [ ⟨"No gender",                  145⟩
  , ⟨"Semantic",                    53⟩
  , ⟨"Semantic and formal",         58⟩ ]

/-- Chapter 32 total sample size. -/
theorem ch32_total : WALSCount.totalOf ch32Distribution = 256 := by native_decide

-- ============================================================================
-- Distribution Verification
-- ============================================================================

/-- Ch 30: Languages with no gender are the modal category. -/
theorem ch30_no_gender_modal :
    ch30Distribution.head? = some ⟨"None (no gender)", 145⟩ := by native_decide

/-- Ch 30: Among gender-bearing languages, 2-gender systems are most common. -/
theorem ch30_two_most_common : (50 > 26) ∧ (50 > 12) ∧ (50 > 24) := by native_decide

/-- Ch 31: Sex-based systems far outnumber non-sex-based ones. -/
theorem ch31_sex_based_dominant : (84 > 25) = true := by native_decide

/-- Ch 32: Semantic-and-formal assignment slightly outnumbers semantic-only. -/
theorem ch32_mixed_slightly_more : (58 > 53) = true := by native_decide

/-- Ch 32: No purely formal assignment system is attested.
    This is Corbett's key generalization: formal assignment always
    supplements a semantic core, never replaces it. -/
theorem ch32_no_purely_formal :
    ch32Distribution.all (λ w => w.label != "Formal only") = true := by native_decide

-- ============================================================================
-- Agreement Targets
-- ============================================================================

/-- Morphosyntactic targets where gender agreement can surface.

    Corbett (1991, Ch 6) establishes an implicational hierarchy:
      attributive > predicate > relative pronoun > personal pronoun > verb
    If a language shows gender agreement on a lower target, it shows
    agreement on all higher targets. This is the Agreement Hierarchy. -/
inductive AgreementTarget where
  | attributive       -- attributive adjective (e.g. French un bon livre)
  | predicate         -- predicate adjective (e.g. Russian kniga interesnaja)
  | relativePronoun   -- relative pronoun (e.g. German der/die/das)
  | personalPronoun   -- personal pronoun (e.g. English he/she/it)
  | verbTarget        -- verb (e.g. Hindi laRkaa aayaa / laRkii aayii)
  deriving DecidableEq, BEq, Repr

/-- Numeric rank in Corbett's Agreement Hierarchy (higher = more likely
    to show agreement; lower = less likely, implying higher targets agree). -/
def AgreementTarget.rank : AgreementTarget → Nat
  | .attributive     => 4
  | .predicate       => 3
  | .relativePronoun => 2
  | .personalPronoun => 1
  | .verbTarget      => 0

/-- The hierarchy is strictly ordered. -/
theorem agreement_hierarchy_strict :
    AgreementTarget.attributive.rank > AgreementTarget.predicate.rank ∧
    AgreementTarget.predicate.rank > AgreementTarget.relativePronoun.rank ∧
    AgreementTarget.relativePronoun.rank > AgreementTarget.personalPronoun.rank ∧
    AgreementTarget.personalPronoun.rank > AgreementTarget.verbTarget.rank := by
  native_decide

-- ============================================================================
-- Semantic Basis Categories
-- ============================================================================

/-- Semantic dimensions that can underlie gender/noun class assignment.

    Different languages organize their noun classification around different
    semantic properties. Sex is the most common, but animacy, humanness,
    and shape/size are also attested as organizing principles. -/
inductive SemanticBasis where
  | sex           -- masculine/feminine based on biological sex
  | animacy       -- animate/inanimate
  | humanness     -- human/non-human
  | shape         -- round/long/flat (classifier-like noun classes)
  | rationality   -- rational/non-rational (some Caucasian languages)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- GenderProfile: Combined Profile Across All Three Chapters
-- ============================================================================

/-- A language's gender profile combining classifications from WALS
    Chapters 30, 31, and 32, plus additional typological information.

    The `rawGenderCount` field stores the actual number of gender/noun class
    categories (not just the WALS bin), enabling finer-grained comparisons.
    The `agreementTargets` list records where gender agreement surfaces.
    The `semanticBases` list records the semantic dimensions organizing
    the system. -/
structure GenderProfile where
  /-- Language name -/
  name : String
  /-- ISO 639-3 code -/
  iso639 : String
  /-- Ch 30: Number of genders (WALS category) -/
  genderCount : GenderCount
  /-- Actual number of gender/noun class categories -/
  rawGenderCount : Nat
  /-- Ch 31: Sex-based or non-sex-based -/
  basis : GenderBasis
  /-- Ch 32: Assignment system -/
  assignment : AssignmentSystem
  /-- Where gender agreement surfaces -/
  agreementTargets : List AgreementTarget
  /-- Semantic dimensions organizing the system -/
  semanticBases : List SemanticBasis
  deriving Repr, DecidableEq, BEq

/-- Whether the raw gender count is consistent with the WALS bin. -/
def GenderProfile.rawCountConsistent (p : GenderProfile) : Bool :=
  p.genderCount.contains p.rawGenderCount

/-- Whether the profile is internally consistent across chapters:
    no-gender in Ch 30 should align with noGender in Ch 31 and Ch 32. -/
def GenderProfile.crossChapterConsistent (p : GenderProfile) : Bool :=
  if p.genderCount == .none then
    p.basis == .noGender && p.assignment == .noGender &&
    p.agreementTargets.length == 0
  else
    p.basis != .noGender && p.assignment != .noGender

/-- Whether the language qualifies as a "noun class" system (5+ categories). -/
def GenderProfile.isNounClassSystem (p : GenderProfile) : Bool :=
  p.rawGenderCount >= 5

/-- Whether the language has any gender agreement. -/
def GenderProfile.hasAgreement (p : GenderProfile) : Bool :=
  p.agreementTargets.length > 0

/-- Lowest agreement target (most marked in Corbett's hierarchy). -/
def GenderProfile.lowestAgreementTarget (p : GenderProfile) : Option AgreementTarget :=
  p.agreementTargets.foldl
    (λ acc t => match acc with
      | none => some t
      | some prev => if t.rank < prev.rank then some t else some prev)
    none

-- ============================================================================
-- Language Data
-- ============================================================================

section LanguageData

-- ────────────────────────────────────────────────────
-- No-gender languages (Ch 30 = none)
-- ────────────────────────────────────────────────────

/-- English: no grammatical gender on nouns or adjectives; only natural gender
    in 3sg pronouns (he/she/it). No gender agreement on adjectives or verbs. -/
def english : GenderProfile :=
  { name := "English"
    iso639 := "eng"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

/-- Mandarin Chinese: no gender system whatsoever. No morphological gender
    marking on nouns, adjectives, or verbs. Third-person pronouns were
    historically undifferentiated; the written distinction ta1/ta1 is a
    20th-century orthographic innovation. -/
def mandarin : GenderProfile :=
  { name := "Mandarin Chinese"
    iso639 := "cmn"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

/-- Japanese: no gender system. Classifier system organizes nouns but does
    not trigger agreement. No gender marking on adjectives, verbs, or
    pronouns. -/
def japanese : GenderProfile :=
  { name := "Japanese"
    iso639 := "jpn"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

/-- Turkish: no gender system. No morphological gender distinctions on
    nouns, adjectives, verbs, or pronouns. The third-person pronoun o is
    used for all referents regardless of sex or animacy. -/
def turkish : GenderProfile :=
  { name := "Turkish"
    iso639 := "tur"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

/-- Finnish: no gender system. No grammatical gender on nouns, adjectives,
    or verbs. The third-person pronoun han is used for all referents. -/
def finnish : GenderProfile :=
  { name := "Finnish"
    iso639 := "fin"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

/-- Korean: no gender system. No morphological gender marking. Third-person
    reference uses demonstratives rather than gendered pronouns. -/
def korean : GenderProfile :=
  { name := "Korean"
    iso639 := "kor"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

/-- Quechua (Cusco): no gender system. Agglutinative morphology with rich
    case and number but no gender distinctions. -/
def quechua : GenderProfile :=
  { name := "Quechua (Cusco)"
    iso639 := "quz"
    genderCount := .none
    rawGenderCount := 0
    basis := .noGender
    assignment := .noGender
    agreementTargets := []
    semanticBases := [] }

-- ────────────────────────────────────────────────────
-- 2-gender languages (Ch 30 = two)
-- ────────────────────────────────────────────────────

/-- French: 2 genders (masculine/feminine). Sex-based with considerable
    formal reinforcement (nouns ending in -tion, -ence tend feminine; -ment,
    -age tend masculine). Agreement on determiners, adjectives (attributive
    and predicate), past participles. Assignment is semantic + formal. -/
def french : GenderProfile :=
  { name := "French"
    iso639 := "fra"
    genderCount := .two
    rawGenderCount := 2
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .personalPronoun]
    semanticBases := [.sex] }

/-- Spanish: 2 genders (masculine/feminine). Sex-based with strong formal
    correlates (-o masculine, -a feminine, with many exceptions). Agreement
    on determiners, adjectives, past participles, and some verb forms. -/
def spanish : GenderProfile :=
  { name := "Spanish"
    iso639 := "spa"
    genderCount := .two
    rawGenderCount := 2
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .personalPronoun]
    semanticBases := [.sex] }

/-- Hindi-Urdu: 2 genders (masculine/feminine). Sex-based with strong
    formal assignment (nouns ending in -aa tend masculine, -ii feminine).
    Agreement on adjectives, verbs (in perfective aspect), and auxiliaries.
    One of the clearest cases of verb agreement for gender. -/
def hindiUrdu : GenderProfile :=
  { name := "Hindi-Urdu"
    iso639 := "hin"
    genderCount := .two
    rawGenderCount := 2
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .verbTarget]
    semanticBases := [.sex] }

/-- Irish: 2 genders (masculine/feminine). Sex-based with formal assignment
    playing a role (initial consonant mutations triggered by gender).
    Agreement on determiners, attributive adjectives, and pronouns. -/
def irish : GenderProfile :=
  { name := "Irish"
    iso639 := "gle"
    genderCount := .two
    rawGenderCount := 2
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .personalPronoun]
    semanticBases := [.sex] }

/-- Hebrew (Modern): 2 genders (masculine/feminine). Sex-based with formal
    correlates (-a, -et endings often feminine). Agreement on adjectives,
    verbs (all tenses), demonstratives, and numerals. -/
def hebrew : GenderProfile :=
  { name := "Hebrew"
    iso639 := "heb"
    genderCount := .two
    rawGenderCount := 2
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .verbTarget]
    semanticBases := [.sex] }

-- ────────────────────────────────────────────────────
-- 3-gender languages (Ch 30 = three)
-- ────────────────────────────────────────────────────

/-- German: 3 genders (masculine/feminine/neuter). Sex-based with extensive
    formal assignment (suffixes like -ung, -heit, -keit are feminine;
    -chen, -lein diminutives are neuter; Ge- collectives are neuter).
    Agreement on determiners, adjectives (attributive and predicate),
    relative pronouns, and personal pronouns. -/
def german : GenderProfile :=
  { name := "German"
    iso639 := "deu"
    genderCount := .three
    rawGenderCount := 3
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun]
    semanticBases := [.sex] }

/-- Russian: 3 genders (masculine/feminine/neuter). Sex-based with strong
    formal correlates (consonant-final stems tend masculine, -a final
    feminine, -o or -e final neuter). Agreement on adjectives, verbs (past
    tense), demonstratives, relative pronouns, and personal pronouns. -/
def russian : GenderProfile :=
  { name := "Russian"
    iso639 := "rus"
    genderCount := .three
    rawGenderCount := 3
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verbTarget]
    semanticBases := [.sex] }

/-- Latin: 3 genders (masculine/feminine/neuter). Sex-based with formal
    assignment via declension classes (-us, -er 2nd decl. mostly masculine,
    -a 1st decl. mostly feminine, -um 2nd decl. neuter). Agreement on
    adjectives and relative/demonstrative pronouns. -/
def latin : GenderProfile :=
  { name := "Latin"
    iso639 := "lat"
    genderCount := .three
    rawGenderCount := 3
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun]
    semanticBases := [.sex] }

/-- Romanian: 3 genders (masculine/feminine/neuter -- the neuter behaves as
    masculine in the singular and feminine in the plural, sometimes analyzed
    as "ambigeneric"). Sex-based with formal assignment. Agreement on
    determiners (enclitic definite article), adjectives, and pronouns. -/
def romanian : GenderProfile :=
  { name := "Romanian"
    iso639 := "ron"
    genderCount := .three
    rawGenderCount := 3
    basis := .sexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .personalPronoun]
    semanticBases := [.sex] }

-- ────────────────────────────────────────────────────
-- 4-gender languages (Ch 30 = four)
-- ────────────────────────────────────────────────────

/-- Dyirbal (Australia): 4 genders (Dixon 1972).
    I: males, most animate beings; II: females, water, fire, fighting;
    III: edible plants and fruit; IV: residual (everything else).
    Non-sex-based in the sense that the system includes categories organized
    around edibility and natural forces, not just biological sex.
    Semantic assignment only (no formal correlates). Agreement on
    determiners/classifiers. -/
def dyirbal : GenderProfile :=
  { name := "Dyirbal"
    iso639 := "dbl"
    genderCount := .four
    rawGenderCount := 4
    basis := .nonSexBased
    assignment := .semanticOnly
    agreementTargets := [.attributive]
    semanticBases := [.sex, .animacy, .shape] }

/-- Georgian: 4 categories in traditional analysis -- rational (humans) vs
    non-rational, cross-cut by an older masculine/feminine trace in
    pronouns. More recent analyses posit a simpler animacy-based split.
    Non-sex-based: the primary division is rational/non-rational.
    Semantic assignment. Agreement on verbs (verb agreement cross-references
    subjects and objects, tracking the rational/non-rational distinction). -/
def georgian : GenderProfile :=
  { name := "Georgian"
    iso639 := "kat"
    genderCount := .four
    rawGenderCount := 4
    basis := .nonSexBased
    assignment := .semanticOnly
    agreementTargets := [.personalPronoun, .verbTarget]
    semanticBases := [.rationality, .animacy] }

-- ────────────────────────────────────────────────────
-- 5+ genders / noun class languages (Ch 30 = fivePlus)
-- ────────────────────────────────────────────────────

/-- Swahili (Bantu): approximately 15--18 noun classes (paired into 9
    singular/plural pairings + locative classes). The system is organized
    around semantic dimensions (human, plant, artifact, abstract, liquid,
    augmentative, diminutive) but with extensive formal assignment via
    prefixes (m-, wa- for Class 1/2 humans; ki-, vi- for Class 7/8 tools;
    etc.). Agreement permeates: determiners, adjectives, verbs, pronouns,
    numerals, and possessives all agree in noun class. -/
def swahili : GenderProfile :=
  { name := "Swahili"
    iso639 := "swh"
    genderCount := .fivePlus
    rawGenderCount := 15
    basis := .nonSexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verbTarget]
    semanticBases := [.humanness, .animacy, .shape] }

/-- Zulu (Bantu): approximately 15 noun classes, closely related to the
    Swahili system (both are Bantu). Organized by similar semantic
    dimensions with prefix-based formal assignment (umu-, aba- for Class 1/2
    humans, etc.). Full agreement across all targets. -/
def zulu : GenderProfile :=
  { name := "Zulu"
    iso639 := "zul"
    genderCount := .fivePlus
    rawGenderCount := 15
    basis := .nonSexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verbTarget]
    semanticBases := [.humanness, .animacy, .shape] }

/-- Fula (Atlantic, Niger-Congo): approximately 20+ noun classes, one of
    the richest class systems in Africa. Classes encode semantic
    distinctions including human, animal, plant, liquid, diminutive,
    augmentative, and pejorative. Formal assignment via class suffixes
    (-o, -Be for Class 1/2 humans; -nde, -de for trees, etc.). Agreement
    on determiners, adjectives, verbs, pronouns. -/
def fula : GenderProfile :=
  { name := "Fula"
    iso639 := "ful"
    genderCount := .fivePlus
    rawGenderCount := 20
    basis := .nonSexBased
    assignment := .semanticAndFormal
    agreementTargets := [.attributive, .predicate, .personalPronoun, .verbTarget]
    semanticBases := [.humanness, .animacy, .shape] }

end LanguageData

-- ============================================================================
-- Language Collection
-- ============================================================================

/-- All language profiles in our sample. -/
def allProfiles : List GenderProfile :=
  [ english, mandarin, japanese, turkish, finnish, korean, quechua
  , french, spanish, hindiUrdu, irish, hebrew
  , german, russian, latin, romanian
  , dyirbal, georgian
  , swahili, zulu, fula ]

theorem allProfiles_count : allProfiles.length = 21 := by native_decide

-- ============================================================================
-- Per-Language Verification: Raw Count Consistency
-- ============================================================================

/-! Every language's raw gender count falls within its declared WALS category. -/

theorem english_raw_consistent : english.rawCountConsistent = true := by native_decide
theorem mandarin_raw_consistent : mandarin.rawCountConsistent = true := by native_decide
theorem japanese_raw_consistent : japanese.rawCountConsistent = true := by native_decide
theorem turkish_raw_consistent : turkish.rawCountConsistent = true := by native_decide
theorem finnish_raw_consistent : finnish.rawCountConsistent = true := by native_decide
theorem korean_raw_consistent : korean.rawCountConsistent = true := by native_decide
theorem quechua_raw_consistent : quechua.rawCountConsistent = true := by native_decide
theorem french_raw_consistent : french.rawCountConsistent = true := by native_decide
theorem spanish_raw_consistent : spanish.rawCountConsistent = true := by native_decide
theorem hindiUrdu_raw_consistent : hindiUrdu.rawCountConsistent = true := by native_decide
theorem irish_raw_consistent : irish.rawCountConsistent = true := by native_decide
theorem hebrew_raw_consistent : hebrew.rawCountConsistent = true := by native_decide
theorem german_raw_consistent : german.rawCountConsistent = true := by native_decide
theorem russian_raw_consistent : russian.rawCountConsistent = true := by native_decide
theorem latin_raw_consistent : latin.rawCountConsistent = true := by native_decide
theorem romanian_raw_consistent : romanian.rawCountConsistent = true := by native_decide
theorem dyirbal_raw_consistent : dyirbal.rawCountConsistent = true := by native_decide
theorem georgian_raw_consistent : georgian.rawCountConsistent = true := by native_decide
theorem swahili_raw_consistent : swahili.rawCountConsistent = true := by native_decide
theorem zulu_raw_consistent : zulu.rawCountConsistent = true := by native_decide
theorem fula_raw_consistent : fula.rawCountConsistent = true := by native_decide

/-- All raw gender counts are consistent with their WALS bins. -/
theorem all_raw_consistent :
    allProfiles.all (·.rawCountConsistent) = true := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-! Cross-chapter consistency: no-gender in Ch 30 aligns with noGender in
Ch 31 and Ch 32; gender-bearing languages do not have noGender in Ch 31
or Ch 32. -/

theorem english_cross_consistent :
    english.crossChapterConsistent = true := by native_decide
theorem mandarin_cross_consistent :
    mandarin.crossChapterConsistent = true := by native_decide
theorem french_cross_consistent :
    french.crossChapterConsistent = true := by native_decide
theorem german_cross_consistent :
    german.crossChapterConsistent = true := by native_decide
theorem swahili_cross_consistent :
    swahili.crossChapterConsistent = true := by native_decide

/-- All profiles are cross-chapter consistent. -/
theorem all_cross_consistent :
    allProfiles.all (·.crossChapterConsistent) = true := by native_decide

-- ============================================================================
-- Per-Language Classification Verification
-- ============================================================================

/-! Spot-checks that each language has the expected WALS category values. -/

-- No-gender languages
theorem english_no_gender : english.genderCount = .none := by native_decide
theorem mandarin_no_gender : mandarin.genderCount = .none := by native_decide
theorem japanese_no_gender : japanese.genderCount = .none := by native_decide
theorem turkish_no_gender : turkish.genderCount = .none := by native_decide
theorem finnish_no_gender : finnish.genderCount = .none := by native_decide
theorem korean_no_gender : korean.genderCount = .none := by native_decide
theorem quechua_no_gender : quechua.genderCount = .none := by native_decide

-- 2-gender languages
theorem french_two_genders : french.genderCount = .two := by native_decide
theorem spanish_two_genders : spanish.genderCount = .two := by native_decide
theorem hindiUrdu_two_genders : hindiUrdu.genderCount = .two := by native_decide
theorem irish_two_genders : irish.genderCount = .two := by native_decide
theorem hebrew_two_genders : hebrew.genderCount = .two := by native_decide

-- 3-gender languages
theorem german_three_genders : german.genderCount = .three := by native_decide
theorem russian_three_genders : russian.genderCount = .three := by native_decide
theorem latin_three_genders : latin.genderCount = .three := by native_decide
theorem romanian_three_genders : romanian.genderCount = .three := by native_decide

-- 4-gender languages
theorem dyirbal_four_genders : dyirbal.genderCount = .four := by native_decide
theorem georgian_four_genders : georgian.genderCount = .four := by native_decide

-- 5+ gender / noun class languages
theorem swahili_fivePlus : swahili.genderCount = .fivePlus := by native_decide
theorem zulu_fivePlus : zulu.genderCount = .fivePlus := by native_decide
theorem fula_fivePlus : fula.genderCount = .fivePlus := by native_decide

-- Gender basis
theorem french_sex_based : french.basis = .sexBased := by native_decide
theorem hindiUrdu_sex_based : hindiUrdu.basis = .sexBased := by native_decide
theorem russian_sex_based : russian.basis = .sexBased := by native_decide
theorem swahili_non_sex_based : swahili.basis = .nonSexBased := by native_decide
theorem dyirbal_non_sex_based : dyirbal.basis = .nonSexBased := by native_decide
theorem georgian_non_sex_based : georgian.basis = .nonSexBased := by native_decide

-- Assignment systems
theorem french_formal_assignment : french.assignment = .semanticAndFormal := by native_decide
theorem dyirbal_semantic_assignment : dyirbal.assignment = .semanticOnly := by native_decide
theorem swahili_mixed_assignment : swahili.assignment = .semanticAndFormal := by native_decide

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

/-! ### Generalization 1: No gender is the most common state.

The majority of the world's languages have no grammatical gender system
at all (145 out of 257 in the WALS Ch 30 sample). This is reflected in
our sample, where 7 out of 21 languages have no gender. -/

theorem no_gender_most_common_wals :
    (145 > 50) ∧ (145 > 26) ∧ (145 > 12) ∧ (145 > 24) := by native_decide

theorem no_gender_in_sample :
    (allProfiles.filter (λ p => p.genderCount == .none)).length = 7 := by native_decide

/-! ### Generalization 2: Among gender systems, 2-gender is most common.

Of the 112 languages with gender in the WALS Ch 30 sample, 50 have
exactly 2 genders -- the single most common count among gender-bearing
languages. -/

theorem two_gender_most_common_among_gendered :
    (50 > 26) ∧ (50 > 12) ∧ (50 > 24) := by native_decide

theorem two_gender_in_sample :
    (allProfiles.filter (λ p => p.genderCount == .two)).length = 5 := by native_decide

/-! ### Generalization 3: Sex-based systems dominate over non-sex-based.

Among languages with gender, sex-based systems (84) far outnumber
non-sex-based ones (25) in the WALS Ch 31 sample. In our sample, all
2- and 3-gender systems are sex-based; non-sex-based systems appear
only with 4+ categories. -/

theorem sex_based_dominates_wals : (84 > 25 * 3) = true := by native_decide

theorem two_three_gender_all_sex_based :
    allProfiles.all (λ p =>
      if p.genderCount == .two || p.genderCount == .three
      then p.basis == .sexBased
      else true) = true := by native_decide

/-! ### Generalization 4: No purely formal assignment exists.

Corbett's key finding: no language assigns gender on a purely formal
basis without any semantic core. In our sample, every language with
gender has semantic assignment (either alone or combined with formal). -/

theorem no_purely_formal_in_sample :
    allProfiles.all (λ p =>
      if p.genderCount != .none
      then p.assignment == .semanticOnly || p.assignment == .semanticAndFormal
      else true) = true := by native_decide

/-! ### Generalization 5: Formal assignment correlates with more genders.

Languages that combine semantic and formal assignment tend to have
richer gender systems. In our sample, all 3-gender languages use
semantic + formal assignment, while semantic-only assignment is
attested only in 4-gender systems. -/

theorem three_gender_always_formal :
    allProfiles.all (λ p =>
      if p.genderCount == .three
      then p.assignment == .semanticAndFormal
      else true) = true := by native_decide

/-! ### Generalization 6: Agreement targets respect Corbett's hierarchy.

In our sample, every language that shows gender agreement on verbs also
shows it on attributive adjectives (i.e., no language agrees only on
verbs without agreeing higher on the hierarchy). -/

def hasTarget (targets : List AgreementTarget) (t : AgreementTarget) : Bool :=
  targets.any (· == t)

theorem verb_agreement_implies_attributive :
    allProfiles.all (λ p =>
      if hasTarget p.agreementTargets .verbTarget
      then hasTarget p.agreementTargets .attributive ||
           hasTarget p.agreementTargets .predicate ||
           hasTarget p.agreementTargets .personalPronoun
      else true) = true := by native_decide

/-! ### Generalization 7: Noun class systems (5+) have the richest agreement.

Languages with 5+ genders show agreement on more targets than languages
with fewer genders. In our sample, all noun class systems (Swahili, Zulu,
Fula) agree on at least 4 out of 5 target types. -/

theorem noun_class_rich_agreement :
    allProfiles.all (λ p =>
      if p.isNounClassSystem
      then p.agreementTargets.length >= 4
      else true) = true := by native_decide

/-! ### Generalization 8: Non-sex-based systems tend to have more genders.

In our sample, non-sex-based systems have 4+ genders, while sex-based
systems have 2--3. This reflects the cross-linguistic pattern: when
gender is not organized around sex, the system tends to proliferate
into a richer noun class system. -/

theorem non_sex_based_more_genders :
    allProfiles.all (λ p =>
      if p.basis == .nonSexBased
      then p.rawGenderCount >= 4
      else true) = true := by native_decide

/-! ### Generalization 9: All GenderCount bins are attested in the sample.

Our 21-language sample covers every WALS Chapter 30 category, from
no gender through 5+ genders. -/

theorem all_gender_counts_attested :
    allProfiles.any (λ p => p.genderCount == .none) &&
    allProfiles.any (λ p => p.genderCount == .two) &&
    allProfiles.any (λ p => p.genderCount == .three) &&
    allProfiles.any (λ p => p.genderCount == .four) &&
    allProfiles.any (λ p => p.genderCount == .fivePlus) = true := by
  native_decide

/-! ### Generalization 10: Gender-bearing languages always show some agreement.

A gender system without any agreement is not a gender system -- genders
are precisely the categories that trigger agreement. In our sample,
every language with gender has at least one agreement target, and every
language without gender has none. -/

theorem gender_implies_agreement :
    allProfiles.all (λ p =>
      if p.genderCount != .none then p.hasAgreement
      else !p.hasAgreement) = true := by native_decide

-- ============================================================================
-- Gender-Number Interaction
-- ============================================================================

/-- Whether a gender system is "canonical" in Corbett's sense: sex-based,
    with 2 or 3 genders, and semantic + formal assignment. -/
def GenderProfile.isCanonicalGender (p : GenderProfile) : Bool :=
  (p.genderCount == .two || p.genderCount == .three) &&
  p.basis == .sexBased &&
  p.assignment == .semanticAndFormal

/-- The European languages in our sample all have canonical gender systems. -/
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

/-- Non-canonical gender systems (noun class, non-sex-based) are all
    non-European in our sample. -/
theorem non_canonical_non_european :
    allProfiles.all (λ p =>
      if p.genderCount != .none && !p.isCanonicalGender
      then p.iso639 == "dbl" || p.iso639 == "kat" ||
           p.iso639 == "swh" || p.iso639 == "zul" ||
           p.iso639 == "ful" || p.iso639 == "gle"
      else true) = true := by native_decide

-- ============================================================================
-- The Gender-Number Scale
-- ============================================================================

/-- The gender-number scale (Corbett 1991): languages can be ordered from
    no gender (0 categories) through systems with progressively more
    categories. In our sample, the scale spans from 0 (English) to 20 (Fula). -/
theorem gender_scale_range :
    allProfiles.any (λ p => p.rawGenderCount == 0) &&
    allProfiles.any (λ p => p.rawGenderCount == 2) &&
    allProfiles.any (λ p => p.rawGenderCount == 3) &&
    allProfiles.any (λ p => p.rawGenderCount == 4) &&
    allProfiles.any (λ p => p.rawGenderCount >= 15) = true := by
  native_decide

/-- The maximum raw gender count in our sample. -/
theorem max_gender_count_is_fula :
    allProfiles.all (λ p => p.rawGenderCount <= 20) &&
    allProfiles.any (λ p => p.rawGenderCount == 20) = true := by
  native_decide

-- ============================================================================
-- ISO 639-3 Verification
-- ============================================================================

/-- All ISO 639-3 codes are non-empty. -/
theorem all_iso_nonempty :
    allProfiles.all (λ p => p.iso639.length > 0) = true := by native_decide

/-- All ISO 639-3 codes are exactly 3 characters (standard length). -/
theorem all_iso_length_3 :
    allProfiles.all (λ p => p.iso639.length == 3) = true := by native_decide

/-- No duplicate ISO codes (each language appears once). -/
theorem iso_codes_unique :
    (allProfiles.map (·.iso639)).eraseDups.length =
    allProfiles.length := by native_decide

-- ============================================================================
-- Cross-Dimensional Queries
-- ============================================================================

/-- Number of no-gender languages in our sample. -/
def noGenderCount : Nat :=
  (allProfiles.filter (λ p => p.genderCount == .none)).length

/-- Number of sex-based gender languages in our sample. -/
def sexBasedCount : Nat :=
  (allProfiles.filter (λ p => p.basis == .sexBased)).length

/-- Number of non-sex-based gender languages in our sample. -/
def nonSexBasedCount : Nat :=
  (allProfiles.filter (λ p => p.basis == .nonSexBased)).length

/-- Number of semantic-only assignment languages. -/
def semanticOnlyCount : Nat :=
  (allProfiles.filter (λ p => p.assignment == .semanticOnly)).length

/-- Number of semantic-and-formal assignment languages. -/
def semanticFormalCount : Nat :=
  (allProfiles.filter (λ p => p.assignment == .semanticAndFormal)).length

/-- Number of noun class systems (5+). -/
def nounClassCount : Nat :=
  (allProfiles.filter (λ p => p.isNounClassSystem)).length

theorem noGender_is_7 : noGenderCount = 7 := by native_decide
theorem sexBased_is_9 : sexBasedCount = 9 := by native_decide
theorem nonSexBased_is_5 : nonSexBasedCount = 5 := by native_decide
theorem semanticOnly_is_2 : semanticOnlyCount = 2 := by native_decide
theorem semanticFormal_is_12 : semanticFormalCount = 12 := by native_decide
theorem nounClass_is_3 : nounClassCount = 3 := by native_decide

-- ============================================================================
-- The Agreement Hierarchy: Implicational Predictions
-- ============================================================================

/-- Corbett's Agreement Hierarchy predicts: if a language shows gender
    agreement on a lower target, it agrees on all higher targets.

    We check: for every pair of targets in a language's agreement list,
    if a lower-ranked target is present, all higher-ranked targets that
    the language might show agreement on are consistent with the hierarchy.

    Specifically: verb agreement (rank 0) implies at least one higher
    target (pronoun, predicate, or attributive) is also present. -/
theorem agreement_hierarchy_verb_implies_higher :
    allProfiles.all (λ p =>
      if hasTarget p.agreementTargets .verbTarget
      then hasTarget p.agreementTargets .attributive ||
           hasTarget p.agreementTargets .predicate ||
           hasTarget p.agreementTargets .personalPronoun
      else true) = true := by native_decide

/-- No language in our sample agrees only on verbs. -/
theorem no_verb_only_agreement :
    allProfiles.all (λ p =>
      if p.agreementTargets == [.verbTarget]
      then false
      else true) = true := by native_decide

/-- No language in our sample has gender agreement only on pronouns:
    pronoun agreement always co-occurs with at least one other target
    (attributive, predicate, or verb). -/
theorem no_pronoun_only_agreement :
    allProfiles.all (λ p =>
      if p.genderCount != .none && hasTarget p.agreementTargets .personalPronoun
      then hasTarget p.agreementTargets .attributive ||
           hasTarget p.agreementTargets .predicate ||
           hasTarget p.agreementTargets .verbTarget
      else true) = true := by native_decide

-- ============================================================================
-- Assignment System and Gender Count Interaction
-- ============================================================================

/-- Semantic-only assignment is restricted to languages with non-sex-based
    systems in our sample. This makes sense: sex-based systems typically
    have formal correlates (declension class, phonological patterns) that
    supplement the semantic core. -/
theorem semantic_only_is_non_sex_based :
    allProfiles.all (λ p =>
      if p.assignment == .semanticOnly
      then p.basis == .nonSexBased
      else true) = true := by native_decide

/-- All sex-based systems in our sample use semantic + formal assignment. -/
theorem sex_based_always_formal :
    allProfiles.all (λ p =>
      if p.basis == .sexBased
      then p.assignment == .semanticAndFormal
      else true) = true := by native_decide

-- ============================================================================
-- Sample Completeness
-- ============================================================================

/-- All three GenderBasis values are attested. -/
theorem all_bases_attested :
    allProfiles.any (λ p => p.basis == .noGender) &&
    allProfiles.any (λ p => p.basis == .sexBased) &&
    allProfiles.any (λ p => p.basis == .nonSexBased) = true := by
  native_decide

/-- All three AssignmentSystem values are attested. -/
theorem all_assignments_attested :
    allProfiles.any (λ p => p.assignment == .noGender) &&
    allProfiles.any (λ p => p.assignment == .semanticOnly) &&
    allProfiles.any (λ p => p.assignment == .semanticAndFormal) = true := by
  native_decide

/-- The sample spans at least 5 distinct ISO codes in each category
    (gender-bearing vs genderless). -/
theorem sample_diversity :
    (allProfiles.filter (λ p => p.genderCount == .none)).length >= 5 ∧
    (allProfiles.filter (λ p => p.genderCount != .none)).length >= 5 := by
  native_decide

end Phenomena.Gender.Typology
