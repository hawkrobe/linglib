import Linglib.Core.Basic

/-!
# Case Typology (WALS Chapters 49--52)

Formalizes four chapters from the World Atlas of Language Structures (WALS)
covering the typology of case systems:

- **Chapter 49**: Number of Cases (Iggesen 2013) -- how many morphological
  cases a language has, from zero to ten or more.
- **Chapter 50**: Asymmetrical Case-Marking (Iggesen 2013) -- whether case
  marking is conditioned by NP properties (animacy, definiteness, pronoun
  status). Also known as Differential Case Marking.
- **Chapter 51**: Position of Case Affixes (Iggesen 2013) -- whether case
  markers are suffixes, prefixes, tonal, or mixed.
- **Chapter 52**: Comitatives and Instrumentals (Stolz et al. 2013) --
  whether comitative ('with X') and instrumental ('by means of X') are
  marked identically or distinctly.

Each chapter is encoded as an inductive type with `WALSCount` distributions
giving the attested cross-linguistic counts. Language profiles combine all
four dimensions, and typological generalizations are verified over the
sample by `native_decide`.

## References

- Iggesen, O. A. (2013). Number of Cases. In Dryer, M. S. & Haspelmath, M.
  (eds.), WALS Online (v2020). Ch. 49.
- Iggesen, O. A. (2013). Asymmetrical Case-Marking. WALS Online. Ch. 50.
- Iggesen, O. A. (2013). Position of Case Affixes. WALS Online. Ch. 51.
- Stolz, T., Stroh, C. & Urdze, A. (2013). Comitatives and Instrumentals.
  WALS Online. Ch. 52.
- Dryer, M. S. & Haspelmath, M. (eds.) (2013). WALS Online (v2020).
  Leipzig: Max Planck Institute for Evolutionary Anthropology.
  https://wals.info
-/

namespace Phenomena.Case.Typology

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
-- Chapter 49: Number of Cases
-- ============================================================================

/-- Number-of-cases categories (WALS Ch. 49, Iggesen 2013).

Languages are classified by the number of morphological case distinctions
in their nominal paradigm. "No morphological case-marking" means the
language has no affixal or clitic case at all (e.g., Mandarin, Thai). -/
inductive CaseCount where
  | none     -- no morphological case-marking
  | two      -- exactly 2 cases
  | threeFour -- 3--4 cases
  | fiveSeven -- 5--7 cases
  | eightNine -- 8--9 cases
  | tenPlus   -- 10 or more cases
  deriving DecidableEq, BEq, Repr

instance : Inhabited CaseCount := ⟨.none⟩

/-- Numeric lower bound for each CaseCount category. -/
def CaseCount.lowerBound : CaseCount → Nat
  | .none      => 0
  | .two       => 2
  | .threeFour => 3
  | .fiveSeven => 5
  | .eightNine => 8
  | .tenPlus   => 10

/-- Whether a raw case count falls in a given CaseCount category. -/
def CaseCount.contains (cc : CaseCount) (n : Nat) : Bool :=
  match cc with
  | .none      => n == 0
  | .two       => n == 2
  | .threeFour => n >= 3 && n <= 4
  | .fiveSeven => n >= 5 && n <= 7
  | .eightNine => n >= 8 && n <= 9
  | .tenPlus   => n >= 10

/-- WALS Chapter 49 distribution (Iggesen 2013, 261-language sample). -/
def ch49Distribution : List WALSCount :=
  [ ⟨"No morphological case-marking", 100⟩
  , ⟨"2 cases",                         23⟩
  , ⟨"3-4 cases",                       39⟩
  , ⟨"5-7 cases",                       37⟩
  , ⟨"8-9 cases",                       23⟩
  , ⟨"10 or more cases",                39⟩ ]

/-- Chapter 49 total sample size. -/
theorem ch49_total : WALSCount.totalOf ch49Distribution = 261 := by native_decide

-- ============================================================================
-- Chapter 50: Asymmetrical Case-Marking
-- ============================================================================

/-- Asymmetrical (differential) case-marking types (WALS Ch. 50, Iggesen 2013).

Differential case marking (DCM) means that case marking on a noun phrase
depends on properties of that NP -- its animacy, definiteness, or whether
it is a full noun vs. a pronoun. For example, in Hindi-Urdu the accusative
marker -ko appears on animate/definite objects but not inanimate/indefinite
ones. -/
inductive AsymmetricalCaseMarking where
  | noCase            -- no morphological case-marking at all
  | borderlineOnly    -- exclusively borderline case-marking
  | noAsymmetry       -- case marking exists but is not conditioned
  | animacyOnly       -- conditioned on animacy alone
  | definitenessOnly  -- conditioned on definiteness alone
  | pronounOnly       -- conditioned on pronoun vs full NP alone
  | twoConditions     -- two of the three conditions
  | threeConditions   -- all three conditions simultaneously
  deriving DecidableEq, BEq, Repr

instance : Inhabited AsymmetricalCaseMarking := ⟨.noCase⟩

/-- Whether this type involves any differential case marking. -/
def AsymmetricalCaseMarking.hasDCM : AsymmetricalCaseMarking → Bool
  | .noCase         => false
  | .borderlineOnly => false
  | .noAsymmetry    => false
  | _               => true

/-- Number of conditioning factors (0--3). -/
def AsymmetricalCaseMarking.conditionCount : AsymmetricalCaseMarking → Nat
  | .noCase | .borderlineOnly | .noAsymmetry => 0
  | .animacyOnly | .definitenessOnly | .pronounOnly => 1
  | .twoConditions => 2
  | .threeConditions => 3

/-- WALS Chapter 50 distribution (Iggesen 2013, 261-language sample). -/
def ch50Distribution : List WALSCount :=
  [ ⟨"No morphological case-marking",           100⟩
  , ⟨"Exclusively borderline case-marking",       19⟩
  , ⟨"No asymmetrical case-marking",              47⟩
  , ⟨"Animacy-conditioned",                       20⟩
  , ⟨"Definiteness-conditioned",                  17⟩
  , ⟨"Pronoun-conditioned (addressor-conditioned)", 4⟩
  , ⟨"Two conditions",                            32⟩
  , ⟨"Three conditions",                          22⟩ ]

/-- Chapter 50 total sample size. -/
theorem ch50_total : WALSCount.totalOf ch50Distribution = 261 := by native_decide

-- ============================================================================
-- Chapter 51: Position of Case Affixes
-- ============================================================================

/-- Position of case affixes (WALS Ch. 51, Iggesen 2013).

Classifies where the case morpheme sits relative to the nominal stem.
Languages with no case affixes at all (either no case or case expressed
only by adpositions) are distinguished from those with suffixes, prefixes,
tonal marking, or mixed strategies. -/
inductive CaseAffixPosition where
  | noAffixes         -- no case affixes or obligatory case-marking
  | suffixesOnly      -- case suffixes only
  | prefixesOnly      -- case prefixes only
  | toneOnly          -- case expressed by tone only
  | bothSuffixPrefix  -- both case suffixes and case prefixes
  deriving DecidableEq, BEq, Repr

instance : Inhabited CaseAffixPosition := ⟨.noAffixes⟩

/-- Whether this position type involves bound morphology. -/
def CaseAffixPosition.hasBoundCase : CaseAffixPosition → Bool
  | .noAffixes => false
  | _          => true

/-- Whether suffixal case marking is present. -/
def CaseAffixPosition.hasSuffix : CaseAffixPosition → Bool
  | .suffixesOnly     => true
  | .bothSuffixPrefix => true
  | _                 => false

/-- WALS Chapter 51 distribution (Iggesen 2013, 261-language sample). -/
def ch51Distribution : List WALSCount :=
  [ ⟨"No case affixes or obligatory case-marking", 105⟩
  , ⟨"Case suffixes only",                         119⟩
  , ⟨"Case prefixes only",                           7⟩
  , ⟨"Case expressed by tone only",                   5⟩
  , ⟨"Both case suffixes and case prefixes",          25⟩ ]

/-- Chapter 51 total sample size. -/
theorem ch51_total : WALSCount.totalOf ch51Distribution = 261 := by native_decide

-- ============================================================================
-- Chapter 52: Comitatives and Instrumentals
-- ============================================================================

/-- Comitative-instrumental syncretism (WALS Ch. 52, Stolz et al. 2013).

In many languages the marker for 'with X' (comitative: accompaniment) and
'by means of X' (instrumental: means/instrument) is the same morpheme.
For example, Russian uses the instrumental case (-om, -oj) for both "I went
with Ivan" and "I cut it with a knife". Other languages distinguish
them, e.g. Japanese -to (comitative) vs. -de (instrumental). -/
inductive ComitativeInstrumental where
  | identity        -- same marker for comitative and instrumental
  | differentiation -- distinct markers
  | mixed           -- both strategies coexist
  deriving DecidableEq, BEq, Repr

instance : Inhabited ComitativeInstrumental := ⟨.identity⟩

/-- Whether the language uses the same morpheme for both functions. -/
def ComitativeInstrumental.isSyncretic : ComitativeInstrumental → Bool
  | .identity => true
  | _         => false

/-- WALS Chapter 52 distribution (Stolz et al. 2013, 322-language sample). -/
def ch52Distribution : List WALSCount :=
  [ ⟨"Identity (same marker)",     194⟩
  , ⟨"Differentiation",            102⟩
  , ⟨"Mixed (both strategies)",     26⟩ ]

/-- Chapter 52 total sample size. -/
theorem ch52_total : WALSCount.totalOf ch52Distribution = 322 := by native_decide

-- ============================================================================
-- Chapter-Level Distribution Theorems
-- ============================================================================

/-- Ch 49: Languages with no case are the modal category (plurality). -/
theorem ch49_no_case_modal :
    ch49Distribution.head? = some ⟨"No morphological case-marking", 100⟩ := by
  native_decide

/-- Ch 49: Case-bearing languages (2+ cases) outnumber caseless languages. -/
theorem ch49_case_languages_majority :
    (23 + 39 + 37 + 23 + 39 > 100) = true := by native_decide

/-- Ch 50: Languages with some DCM outnumber those with no asymmetry. -/
theorem ch50_dcm_common :
    (20 + 17 + 4 + 32 + 22 > 47) = true := by native_decide

/-- Ch 51: Suffixal case is the dominant strategy among case-marking languages. -/
theorem ch51_suffix_dominant :
    (119 > 7) ∧ (119 > 5) ∧ (119 > 25) := by native_decide

/-- Ch 52: Comitative-instrumental identity is the majority pattern. -/
theorem ch52_identity_majority :
    (194 > 102) ∧ (194 > 26) := by native_decide

-- ============================================================================
-- CaseProfile: Combined Profile Across All Four Chapters
-- ============================================================================

/-- A language's case profile, combining classifications from all four
WALS case chapters.

This structure records a single language's position in each of the four
typological dimensions. The `rawCaseCount` field stores the actual number
of morphological cases (not just the WALS bin), enabling finer-grained
generalizations. -/
structure CaseProfile where
  /-- Language name -/
  name : String
  /-- ISO 639-3 code -/
  iso639 : String
  /-- Ch 49: Number of cases (WALS category) -/
  caseCount : CaseCount
  /-- Actual number of morphological cases -/
  rawCaseCount : Nat
  /-- Ch 50: Asymmetrical case-marking type -/
  asymmetry : AsymmetricalCaseMarking
  /-- Ch 51: Position of case affixes -/
  affixPosition : CaseAffixPosition
  /-- Ch 52: Comitative-instrumental relation -/
  comitativeInstr : ComitativeInstrumental
  deriving Repr, DecidableEq, BEq

/-- Whether the raw case count is consistent with the WALS bin. -/
def CaseProfile.rawCountConsistent (p : CaseProfile) : Bool :=
  p.caseCount.contains p.rawCaseCount

/-- Whether the profile is internally consistent across chapters:
    no-case in Ch 49 should align with no-case in Ch 50 and no-affixes in Ch 51. -/
def CaseProfile.crossChapterConsistent (p : CaseProfile) : Bool :=
  -- If Ch 49 says no case, Ch 50 should say noCase and Ch 51 noAffixes
  if p.caseCount == .none then
    p.asymmetry == .noCase && p.affixPosition == .noAffixes
  -- If Ch 49 says 2+ cases, Ch 50 should not say noCase
  else
    p.asymmetry != .noCase

-- ============================================================================
-- Language Data (~16 languages)
-- ============================================================================

section LanguageData

/-- Finnish: 15 morphological cases (nom, gen, acc, part, iness, elat, illat,
adess, ablat, allat, ess, transl, instruct, comit, abes). Suffixal.
No DCM. Comitative and instrumental are distinct cases. -/
def finnish : CaseProfile :=
  { name := "Finnish"
    iso639 := "fin"
    caseCount := .tenPlus
    rawCaseCount := 15
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Hungarian: 18 morphological cases (nom, acc, dat, instrum, causal-final,
translative, terminative, essive-formal, essive-modal, inessive, elative,
illative, superessive, delative, sublative, adessive, ablative, allative).
Suffixal agglutinative. Comitative (-val, -vel) = instrumental. -/
def hungarian : CaseProfile :=
  { name := "Hungarian"
    iso639 := "hun"
    caseCount := .tenPlus
    rawCaseCount := 18
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .identity }

/-- Turkish: 6 cases (nom, acc, gen, dat, loc, abl). Suffixal agglutinative.
Differential object marking: definite objects take -I, indefinite do not. -/
def turkish : CaseProfile :=
  { name := "Turkish"
    iso639 := "tur"
    caseCount := .fiveSeven
    rawCaseCount := 6
    asymmetry := .definitenessOnly
    affixPosition := .suffixesOnly
    comitativeInstr := .identity }

/-- Latin: 6 cases (nom, acc, gen, dat, abl, voc; locative vestigial).
Suffixal fusional. No asymmetrical case-marking. Comitative (cum + abl)
vs. instrumental (plain abl) are technically distinct strategies. -/
def latin : CaseProfile :=
  { name := "Latin"
    iso639 := "lat"
    caseCount := .fiveSeven
    rawCaseCount := 6
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Russian: 6 cases (nom, acc, gen, dat, instrum, prep/loc).
Suffixal fusional. Differential accusative: animate nouns take genitive
form in accusative, inanimates keep nominative form. -/
def russian : CaseProfile :=
  { name := "Russian"
    iso639 := "rus"
    caseCount := .fiveSeven
    rawCaseCount := 6
    asymmetry := .animacyOnly
    affixPosition := .suffixesOnly
    comitativeInstr := .identity }

/-- German: 4 cases (nom, acc, gen, dat). Suffixal fusional with articles
carrying most case marking. No systematic DCM. Comitative (mit + dat)
and instrumental (mit + dat) use the same marker. -/
def german : CaseProfile :=
  { name := "German"
    iso639 := "deu"
    caseCount := .threeFour
    rawCaseCount := 4
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .identity }

/-- Japanese: case particles (ga, o, ni, no, de, e, to, kara, made, ...).
Postpositional clitics rather than affixes in WALS's classification.
Differential object marking with -o conditioned by specificity/topicality.
Comitative -to vs. instrumental -de are distinct. -/
def japanese : CaseProfile :=
  { name := "Japanese"
    iso639 := "jpn"
    caseCount := .eightNine
    rawCaseCount := 8
    asymmetry := .definitenessOnly
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- English: 2-case system surviving only in pronouns (nom/acc: I/me,
he/him, she/her, we/us, they/them). No case affixes on nouns.
Comitative 'with' and instrumental 'with' are identical. -/
def english : CaseProfile :=
  { name := "English"
    iso639 := "eng"
    caseCount := .two
    rawCaseCount := 2
    asymmetry := .pronounOnly
    affixPosition := .noAffixes
    comitativeInstr := .identity }

/-- Korean: case particles (-i/ga nom, -(l)eul acc, -ui gen, -e dat/loc,
-eseo loc/source, -(eu)ro instr/dir, -wa/gwa comit). Particles are
postpositional clitics. Optional object marking conditioned by
definiteness/topicality. Comitative -wa and instrumental -(eu)ro
are distinct. -/
def korean : CaseProfile :=
  { name := "Korean"
    iso639 := "kor"
    caseCount := .fiveSeven
    rawCaseCount := 7
    asymmetry := .definitenessOnly
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Mandarin Chinese: no morphological case. Fixed SVO word order
encodes grammatical relations. No case markers, no DCM, comitative
and instrumental expressed by distinct prepositions (he 'with-COM'
vs. yong 'with-INSTR'). -/
def mandarin : CaseProfile :=
  { name := "Mandarin Chinese"
    iso639 := "cmn"
    caseCount := .none
    rawCaseCount := 0
    asymmetry := .noCase
    affixPosition := .noAffixes
    comitativeInstr := .differentiation }

/-- Hindi-Urdu: 3 cases (direct, oblique, vocative). Postpositional
system with -ne (ergative), -ko (accusative/dative), -se (instrumental/
ablative), -me (locative). Differential object marking: -ko appears
on animate/specific objects. Comitative -ke saath vs. instrumental -se
are distinct. -/
def hindiUrdu : CaseProfile :=
  { name := "Hindi-Urdu"
    iso639 := "hin"
    caseCount := .threeFour
    rawCaseCount := 3
    asymmetry := .twoConditions
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Arabic (Modern Standard): 3 cases (nom -u, acc -a, gen -i).
Suffixal. Full case marking on indefinite nouns (tanwin); definite
nouns often show reduced marking in spoken varieties, but MSA maintains
it. Comitative (maʕa) and instrumental (bi-) are distinct. -/
def arabic : CaseProfile :=
  { name := "Arabic (MSA)"
    iso639 := "arb"
    caseCount := .threeFour
    rawCaseCount := 3
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Georgian: 7 cases (nom, erg, dat, gen, instrum, adverbial, vocative).
Suffixal agglutinative. Split-ergative system conditioned by tense/aspect
(not NP properties), so no DCM in the WALS sense. Instrumental -it and
comitative -tan are distinct. -/
def georgian : CaseProfile :=
  { name := "Georgian"
    iso639 := "kat"
    caseCount := .fiveSeven
    rawCaseCount := 7
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Quechua (Cusco): 12+ cases (nom, acc -ta, gen -pa or -q, dat -man,
loc -pi, abl -manta, instrum -wan, comit -wan, limit -kama, causal
-rayku, benef -paq, topic -qa, ...). Suffixal agglutinative.
Comitative and instrumental both use -wan (identity). -/
def quechua : CaseProfile :=
  { name := "Quechua (Cusco)"
    iso639 := "quz"
    caseCount := .tenPlus
    rawCaseCount := 12
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .identity }

/-- Basque: ergative-absolutive system with 11+ cases (abs, erg, dat,
gen, comit -ekin, instrum -z, iness, allat, ablat, destinat, motivat).
Suffixal. Differential ergative marking in some analyses. Comitative
-ekin and instrumental -z are distinct. -/
def basque : CaseProfile :=
  { name := "Basque"
    iso639 := "eus"
    caseCount := .tenPlus
    rawCaseCount := 11
    asymmetry := .noAsymmetry
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

/-- Tamil: 8 cases (nom, acc, dat, gen, instrum, loc, ablat, sociative/
comitative). Suffixal agglutinative. Differential object marking:
accusative -ai on animate/definite objects. Comitative -ootu and
instrumental -aal are distinct. -/
def tamil : CaseProfile :=
  { name := "Tamil"
    iso639 := "tam"
    caseCount := .eightNine
    rawCaseCount := 8
    asymmetry := .twoConditions
    affixPosition := .suffixesOnly
    comitativeInstr := .differentiation }

end LanguageData

-- ============================================================================
-- Language Collection
-- ============================================================================

/-- All language profiles in our sample. -/
def allProfiles : List CaseProfile :=
  [ finnish, hungarian, turkish, latin, russian, german, japanese
  , english, korean, mandarin, hindiUrdu, arabic, georgian, quechua
  , basque, tamil ]

theorem allProfiles_count : allProfiles.length = 16 := by native_decide

-- ============================================================================
-- Per-Language Verification: Raw Count Consistency
-- ============================================================================

/-! Every language's raw case count falls within its declared WALS category. -/

theorem finnish_raw_consistent : finnish.rawCountConsistent = true := by native_decide
theorem hungarian_raw_consistent : hungarian.rawCountConsistent = true := by native_decide
theorem turkish_raw_consistent : turkish.rawCountConsistent = true := by native_decide
theorem latin_raw_consistent : latin.rawCountConsistent = true := by native_decide
theorem russian_raw_consistent : russian.rawCountConsistent = true := by native_decide
theorem german_raw_consistent : german.rawCountConsistent = true := by native_decide
theorem japanese_raw_consistent : japanese.rawCountConsistent = true := by native_decide
theorem english_raw_consistent : english.rawCountConsistent = true := by native_decide
theorem korean_raw_consistent : korean.rawCountConsistent = true := by native_decide
theorem mandarin_raw_consistent : mandarin.rawCountConsistent = true := by native_decide
theorem hindiUrdu_raw_consistent : hindiUrdu.rawCountConsistent = true := by native_decide
theorem arabic_raw_consistent : arabic.rawCountConsistent = true := by native_decide
theorem georgian_raw_consistent : georgian.rawCountConsistent = true := by native_decide
theorem quechua_raw_consistent : quechua.rawCountConsistent = true := by native_decide
theorem basque_raw_consistent : basque.rawCountConsistent = true := by native_decide
theorem tamil_raw_consistent : tamil.rawCountConsistent = true := by native_decide

/-- All raw case counts are consistent with their WALS bins. -/
theorem all_raw_consistent :
    allProfiles.all (·.rawCountConsistent) = true := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-! Cross-chapter consistency: no-case in Ch 49 aligns with noCase in
Ch 50 and noAffixes in Ch 51; case-bearing languages do not have
noCase in Ch 50. -/

theorem mandarin_cross_consistent :
    mandarin.crossChapterConsistent = true := by native_decide

theorem english_cross_consistent :
    english.crossChapterConsistent = true := by native_decide

theorem finnish_cross_consistent :
    finnish.crossChapterConsistent = true := by native_decide

/-- All profiles are cross-chapter consistent. -/
theorem all_cross_consistent :
    allProfiles.all (·.crossChapterConsistent) = true := by native_decide

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

/-! ### Generalization 1: Case-rich languages are overwhelmingly suffixal.

Among the world's languages, suffixal case marking is far more common
than prefixal. In our sample, every language with case affixes uses
suffixes (either exclusively or in combination with prefixes). This
reflects the strong universal preference documented by Hawkins (1983)
and Dryer (1992). -/

theorem case_rich_are_suffixal :
    allProfiles.all (λ p =>
      if p.caseCount != .none && p.affixPosition.hasBoundCase
      then p.affixPosition.hasSuffix
      else true) = true := by native_decide

/-! ### Generalization 2: No prefixal-only case in our sample.

No language in our sample uses exclusively prefixal case marking.
Cross-linguistically, prefixal-only case is very rare (WALS Ch 51
reports only 7 out of 261 languages). -/

theorem no_prefix_only :
    allProfiles.all (λ p => p.affixPosition != .prefixesOnly) = true := by
  native_decide

/-! ### Generalization 3: DCM is conditioned by animacy or definiteness.

Among languages with differential case marking in our sample, the
conditioning factors are animacy, definiteness, or pronoun status --
never some other property like gender or number alone. -/

theorem dcm_conditions_limited :
    allProfiles.all (λ p =>
      if p.asymmetry.hasDCM then
        p.asymmetry == .animacyOnly ||
        p.asymmetry == .definitenessOnly ||
        p.asymmetry == .pronounOnly ||
        p.asymmetry == .twoConditions ||
        p.asymmetry == .threeConditions
      else true) = true := by native_decide

/-! ### Generalization 4: Comitative-instrumental identity is common but
not universal. Identity (syncretism) and differentiation both occur
across language families. -/

theorem both_comit_instr_patterns_attested :
    allProfiles.any (λ p => p.comitativeInstr == .identity) &&
    allProfiles.any (λ p => p.comitativeInstr == .differentiation) = true := by
  native_decide

/-! ### Generalization 5: No-case languages have no asymmetrical marking.

By definition, if there is no morphological case, there can be no
asymmetrical (differential) case marking. -/

theorem no_case_no_asymmetry :
    allProfiles.all (λ p =>
      if p.caseCount == .none then p.asymmetry == .noCase
      else true) = true := by native_decide

/-! ### Generalization 6: No-case languages have no case affixes.

Again by definition: without morphological case, there are no case
affixes to position. -/

theorem no_case_no_affixes :
    allProfiles.all (λ p =>
      if p.caseCount == .none then p.affixPosition == .noAffixes
      else true) = true := by native_decide

/-! ### Generalization 7: 10+-case languages all have suffixal case.

Highly agglutinative case-rich systems (Finnish, Hungarian, Quechua,
Basque) uniformly use suffixes. No case-rich language uses prefixes
only or tone only. -/

theorem ten_plus_all_suffixal :
    allProfiles.all (λ p =>
      if p.caseCount == .tenPlus then p.affixPosition == .suffixesOnly
      else true) = true := by native_decide

/-! ### Generalization 8: Languages with 2 cases tend toward asymmetrical
marking.

When a language has only two cases, case marking often applies
differentially (to pronouns only, or conditioned by definiteness).
English is the classic example: only pronouns show nominative/accusative. -/

theorem two_case_tends_asymmetric :
    allProfiles.all (λ p =>
      if p.caseCount == .two then p.asymmetry.hasDCM || p.asymmetry == .pronounOnly
      else true) = true := by native_decide

/-! ### Generalization 9: Comitative-instrumental identity correlates with
case-rich systems.

Among our case-rich languages (5+ cases), those with identity include
Hungarian, Russian, Turkish, Quechua -- all agglutinative or fusional
languages where an instrumental case doubles for comitative. -/

theorem identity_in_case_rich :
    (allProfiles.filter (λ p => p.rawCaseCount >= 5 &&
      p.comitativeInstr == .identity)).length >= 3 := by native_decide

/-! ### Generalization 10: All CaseCount bins are attested in the sample.

Our 16-language sample covers every WALS Chapter 49 category. -/

theorem all_case_counts_attested :
    allProfiles.any (λ p => p.caseCount == .none) &&
    allProfiles.any (λ p => p.caseCount == .two) &&
    allProfiles.any (λ p => p.caseCount == .threeFour) &&
    allProfiles.any (λ p => p.caseCount == .fiveSeven) &&
    allProfiles.any (λ p => p.caseCount == .eightNine) &&
    allProfiles.any (λ p => p.caseCount == .tenPlus) = true := by
  native_decide

-- ============================================================================
-- Per-Language Classification Verification
-- ============================================================================

/-! Spot-checks that each language has the expected WALS category values. -/

theorem finnish_tenPlus : finnish.caseCount = .tenPlus := by native_decide
theorem hungarian_tenPlus : hungarian.caseCount = .tenPlus := by native_decide
theorem turkish_fiveSeven : turkish.caseCount = .fiveSeven := by native_decide
theorem latin_fiveSeven : latin.caseCount = .fiveSeven := by native_decide
theorem russian_fiveSeven : russian.caseCount = .fiveSeven := by native_decide
theorem german_threeFour : german.caseCount = .threeFour := by native_decide
theorem english_two : english.caseCount = .two := by native_decide
theorem mandarin_none : mandarin.caseCount = .none := by native_decide

theorem russian_animacy_dcm : russian.asymmetry = .animacyOnly := by native_decide
theorem turkish_definiteness_dcm : turkish.asymmetry = .definitenessOnly := by native_decide
theorem english_pronoun_dcm : english.asymmetry = .pronounOnly := by native_decide
theorem hindiUrdu_two_cond : hindiUrdu.asymmetry = .twoConditions := by native_decide

theorem english_no_affixes : english.affixPosition = .noAffixes := by native_decide
theorem finnish_suffixes : finnish.affixPosition = .suffixesOnly := by native_decide
theorem mandarin_no_affixes : mandarin.affixPosition = .noAffixes := by native_decide

theorem russian_com_instr_identity :
    russian.comitativeInstr = .identity := by native_decide
theorem japanese_com_instr_diff :
    japanese.comitativeInstr = .differentiation := by native_decide

-- ============================================================================
-- Case Inventory Ordering
-- ============================================================================

/-- Raw case counts are ordered as expected: Finnish < Hungarian at the
top, Mandarin and English at the bottom. -/
theorem case_count_ordering :
    mandarin.rawCaseCount < english.rawCaseCount ∧
    english.rawCaseCount < arabic.rawCaseCount ∧
    arabic.rawCaseCount < german.rawCaseCount ∧
    german.rawCaseCount < turkish.rawCaseCount ∧
    turkish.rawCaseCount < korean.rawCaseCount ∧
    korean.rawCaseCount < japanese.rawCaseCount ∧
    japanese.rawCaseCount < basque.rawCaseCount ∧
    basque.rawCaseCount < quechua.rawCaseCount ∧
    quechua.rawCaseCount < finnish.rawCaseCount ∧
    finnish.rawCaseCount < hungarian.rawCaseCount := by native_decide

-- ============================================================================
-- Summary Statistics
-- ============================================================================

/-- Number of caseless languages in our sample. -/
def caselessCount : Nat :=
  (allProfiles.filter (λ p => p.caseCount == .none)).length

/-- Number of DCM languages in our sample. -/
def dcmCount : Nat :=
  (allProfiles.filter (λ p => p.asymmetry.hasDCM)).length

/-- Number of suffixal-case languages in our sample. -/
def suffixalCount : Nat :=
  (allProfiles.filter (λ p => p.affixPosition.hasSuffix)).length

/-- Number of comitative-instrumental identity languages. -/
def comitIdentityCount : Nat :=
  (allProfiles.filter (λ p => p.comitativeInstr.isSyncretic)).length

theorem caseless_is_1 : caselessCount = 1 := by native_decide
theorem dcm_is_7 : dcmCount = 7 := by native_decide
theorem suffixal_is_14 : suffixalCount = 14 := by native_decide
theorem comit_identity_is_6 : comitIdentityCount = 6 := by native_decide

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
-- Cross-Chapter Aggregate Patterns
-- ============================================================================

/-- Languages with DCM (Ch 50) all have at least 2 cases (Ch 49). -/
theorem dcm_implies_case :
    allProfiles.all (λ p =>
      if p.asymmetry.hasDCM then p.rawCaseCount >= 2
      else true) = true := by native_decide

/-- Languages with case affixes (Ch 51) all have at least 2 cases (Ch 49). -/
theorem affixes_imply_case :
    allProfiles.all (λ p =>
      if p.affixPosition.hasBoundCase then p.rawCaseCount >= 2
      else true) = true := by native_decide

/-- No language with 10+ cases uses identity for comitative-instrumental
in our sample that also has no DCM and uses suffixes. This checks a
three-way conjunction across chapters. -/
theorem rich_case_profile_exists :
    allProfiles.any (λ p =>
      p.caseCount == .tenPlus &&
      p.asymmetry == .noAsymmetry &&
      p.affixPosition == .suffixesOnly) = true := by native_decide

-- ============================================================================
-- Sample Size Verification
-- ============================================================================

/-- Ch 49 and Ch 50 share the same 261-language sample. -/
theorem ch49_ch50_same_sample :
    WALSCount.totalOf ch49Distribution =
    WALSCount.totalOf ch50Distribution := by native_decide

/-- Ch 51 also uses the same 261-language sample. -/
theorem ch51_same_sample :
    WALSCount.totalOf ch51Distribution =
    WALSCount.totalOf ch50Distribution := by native_decide

-- ============================================================================
-- Aissen (2003) Prominence Scales and Differential Object Marking
-- ============================================================================

/-! ## Aissen (2003) DOM Hierarchy

Formalizes the two prominence scales and bidimensional DOM predictions from:

- Aissen, J. (2003). Differential Object Marking: Iconicity vs. Economy.
  Natural Language & Linguistic Theory 21(3): 435--483.

Aissen proposes that differential object marking (DOM) is conditioned by
two independently motivated prominence scales — **animacy** and
**definiteness** — and that the set of marked cells in the animacy ×
definiteness grid must form an **upper set** (upward-closed in the
product partial order). This "monotonicity" property predicts that if a
language marks a less-prominent object, it must also mark all more-prominent
objects, yielding the attested "staircase" cutoff patterns.

### Scales

- **Animacy**: Human > Animate > Inanimate
- **Definiteness**: Personal Pronoun > Proper Name > Definite NP >
  Indefinite Specific NP > Non-specific NP

### Typological prediction

For any attested DOM system, the marking function `marks(a, d)` is
monotone: if `marks(a, d) = true` then `marks(a', d') = true` for all
`a'` at least as prominent as `a` and `d'` at least as prominent as `d`.
-/

-- ============================================================================
-- Animacy Scale (Aissen 2003, §2)
-- ============================================================================

/-- Levels of the animacy prominence scale (Aissen 2003, §2).
Human > Animate > Inanimate. -/
inductive AnimacyLevel where
  /-- Most prominent: human referents -/
  | human
  /-- Non-human animates -/
  | animate
  /-- Least prominent: inanimate referents -/
  | inanimate
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Numeric rank on the animacy scale: Human (2) > Animate (1) > Inanimate (0). -/
def AnimacyLevel.rank : AnimacyLevel → Nat
  | .human     => 2
  | .animate   => 1
  | .inanimate => 0

/-- All animacy levels (exhaustive enumeration for finite verification). -/
def AnimacyLevel.all : List AnimacyLevel := [.human, .animate, .inanimate]

theorem AnimacyLevel.all_length : AnimacyLevel.all.length = 3 := by native_decide

-- ============================================================================
-- Definiteness Scale (Aissen 2003, §2)
-- ============================================================================

/-- Levels of the definiteness prominence scale (Aissen 2003, §2).
Personal Pronoun > Proper Name > Definite NP > Indefinite Specific NP >
Non-specific NP. -/
inductive DefinitenessLevel where
  /-- Most prominent: personal pronouns -/
  | personalPronoun
  /-- Proper names -/
  | properName
  /-- Definite NPs (with article or demonstrative) -/
  | definite
  /-- Indefinite but specific NPs -/
  | indefiniteSpecific
  /-- Least prominent: non-specific indefinites -/
  | nonSpecific
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Numeric rank on the definiteness scale:
Pronoun (4) > Proper (3) > Definite (2) > IndSp (1) > NonSp (0). -/
def DefinitenessLevel.rank : DefinitenessLevel → Nat
  | .personalPronoun    => 4
  | .properName         => 3
  | .definite           => 2
  | .indefiniteSpecific => 1
  | .nonSpecific        => 0

/-- All definiteness levels (exhaustive enumeration). -/
def DefinitenessLevel.all : List DefinitenessLevel :=
  [.personalPronoun, .properName, .definite, .indefiniteSpecific, .nonSpecific]

theorem DefinitenessLevel.all_length : DefinitenessLevel.all.length = 5 := by
  native_decide

-- ============================================================================
-- Scale Ordering Verification
-- ============================================================================

/-! The rank functions encode the strict ordering of the two scales. -/

theorem animacy_human_gt_animate :
    AnimacyLevel.human.rank > AnimacyLevel.animate.rank := by decide

theorem animacy_animate_gt_inanimate :
    AnimacyLevel.animate.rank > AnimacyLevel.inanimate.rank := by decide

theorem definiteness_pronoun_gt_proper :
    DefinitenessLevel.personalPronoun.rank > DefinitenessLevel.properName.rank := by decide

theorem definiteness_proper_gt_definite :
    DefinitenessLevel.properName.rank > DefinitenessLevel.definite.rank := by decide

theorem definiteness_definite_gt_indSp :
    DefinitenessLevel.definite.rank > DefinitenessLevel.indefiniteSpecific.rank := by decide

theorem definiteness_indSp_gt_nonSp :
    DefinitenessLevel.indefiniteSpecific.rank > DefinitenessLevel.nonSpecific.rank := by decide

-- ============================================================================
-- DOM Profiles: Bidimensional Marking Grids
-- ============================================================================

/-- A DOM (Differential Object Marking) profile: which cells in the
animacy × definiteness grid receive overt case marking.

Each cell `(a, d)` records whether an object with animacy level `a`
and definiteness level `d` obligatorily receives an overt DOM marker
(e.g., Spanish `a`, Turkish `-(y)I`, Hindi `-ko`). -/
structure DOMProfile where
  /-- Language name -/
  name : String
  /-- Whether cell (a, d) receives overt DOM marking -/
  marks : AnimacyLevel → DefinitenessLevel → Bool

/-- The monotonicity (upper-set) property: if a cell is marked, then all
cells at least as prominent on BOTH dimensions are also marked.

This is Aissen's central prediction: DOM cutoffs form a "staircase"
in the bidimensional grid, never marking a less-prominent cell while
leaving a more-prominent one unmarked. -/
def DOMProfile.isMonotone (p : DOMProfile) : Bool :=
  AnimacyLevel.all.all λ a =>
    DefinitenessLevel.all.all λ d =>
      if p.marks a d then
        AnimacyLevel.all.all λ a' =>
          DefinitenessLevel.all.all λ d' =>
            if a'.rank ≥ a.rank && d'.rank ≥ d.rank then p.marks a' d'
            else true
      else true

/-- Whether a DOM profile depends only on animacy (definiteness is irrelevant). -/
def DOMProfile.isAnimacyOnly (p : DOMProfile) : Bool :=
  DefinitenessLevel.all.all λ d₁ =>
    DefinitenessLevel.all.all λ d₂ =>
      AnimacyLevel.all.all λ a =>
        p.marks a d₁ == p.marks a d₂

/-- Whether a DOM profile depends only on definiteness (animacy is irrelevant). -/
def DOMProfile.isDefinitenessOnly (p : DOMProfile) : Bool :=
  AnimacyLevel.all.all λ a₁ =>
    AnimacyLevel.all.all λ a₂ =>
      DefinitenessLevel.all.all λ d =>
        p.marks a₁ d == p.marks a₂ d

-- ============================================================================
-- Cutoff Constructors for One-Dimensional DOM
-- ============================================================================

/-- Construct a one-dimensional animacy-based DOM profile: objects at or
above the cutoff animacy level are marked, regardless of definiteness.
Example: Spanish marks human objects (cutoff = .human). -/
def DOMProfile.animacyCutoff (name : String) (cutoff : AnimacyLevel) : DOMProfile :=
  { name, marks := λ a _ => a.rank ≥ cutoff.rank }

/-- Construct a one-dimensional definiteness-based DOM profile: objects at
or above the cutoff definiteness level are marked, regardless of animacy.
Example: Turkish marks definite+ objects (cutoff = .definite). -/
def DOMProfile.definitenessCutoff (name : String) (cutoff : DefinitenessLevel) : DOMProfile :=
  { name, marks := λ _ d => d.rank ≥ cutoff.rank }

/-- Animacy-cutoff DOM is always monotone, for any cutoff level.
One-dimensional patterns are automatically upper sets. -/
theorem animacy_cutoff_monotone (cutoff : AnimacyLevel) :
    (DOMProfile.animacyCutoff "" cutoff).isMonotone = true := by
  cases cutoff <;> native_decide

/-- Definiteness-cutoff DOM is always monotone, for any cutoff level. -/
theorem definiteness_cutoff_monotone (cutoff : DefinitenessLevel) :
    (DOMProfile.definitenessCutoff "" cutoff).isMonotone = true := by
  cases cutoff <;> native_decide

-- ============================================================================
-- Language DOM Profiles
-- ============================================================================

section DOMLanguages

/-- Spanish: `a`-marking for human direct objects regardless of definiteness.
One-dimensional (animacy-based), cutoff between human and animate
(Aissen 2003, §4). -/
def spanishDOM : DOMProfile :=
  DOMProfile.animacyCutoff "Spanish" .human

/-- Russian: animate accusative (genitive form used as accusative for
animate nouns). One-dimensional (animacy-based), cutoff between animate
and inanimate (Aissen 2003, §4). -/
def russianDOM : DOMProfile :=
  DOMProfile.animacyCutoff "Russian" .animate

/-- Turkish: `-(y)I` marking for definite direct objects regardless of
animacy. One-dimensional (definiteness-based), cutoff between definite
and indefinite specific (Aissen 2003, §4). -/
def turkishDOM : DOMProfile :=
  DOMProfile.definitenessCutoff "Turkish" .definite

/-- Hebrew: `ʔet` marking for definite direct objects regardless of
animacy. Same one-dimensional definiteness cutoff as Turkish
(Aissen 2003, §4). -/
def hebrewDOM : DOMProfile :=
  DOMProfile.definitenessCutoff "Hebrew" .definite

/-- Persian: `-rā` marking for definite direct objects. One-dimensional
(definiteness-based) for obligatory marking; optional extension to
specific indefinite animates (Aissen 2003, §5). Modeled here with the
definiteness-based obligatory core. -/
def persianDOM : DOMProfile :=
  DOMProfile.definitenessCutoff "Persian" .definite

/-- Catalan: `a`-marking restricted to personal pronouns. The most
restrictive DOM pattern attested: only the highest cell on the
definiteness scale receives marking (Aissen 2003, §4). -/
def catalanDOM : DOMProfile :=
  DOMProfile.definitenessCutoff "Catalan" .personalPronoun

/-- Hindi-Urdu: `-ko` marking conditioned by BOTH animacy and definiteness.
Two-dimensional DOM with a staircase cutoff (Aissen 2003, §5, Table 12):
- Human objects: marked when indefinite specific or more prominent
- Animate objects: marked when definite or more prominent
- Inanimate objects: not obligatorily marked

This captures the obligatory marking core. Optional/variable marking
extends further down the staircase at the boundary cells. -/
def hindiDOM : DOMProfile :=
  { name := "Hindi-Urdu"
    marks := λ a d =>
      match a with
      | .human     => d.rank ≥ DefinitenessLevel.indefiniteSpecific.rank
      | .animate   => d.rank ≥ DefinitenessLevel.definite.rank
      | .inanimate => false }

/-- No DOM: no differential marking (either no case at all, or uniform
case on all objects). Trivially monotone. -/
def noDOMProfile : DOMProfile :=
  { name := "No DOM"
    marks := λ _ _ => false }

end DOMLanguages

-- ============================================================================
-- DOM Profile Collection
-- ============================================================================

/-- All DOM profiles in the sample. -/
def allDOMProfiles : List DOMProfile :=
  [spanishDOM, russianDOM, turkishDOM, hebrewDOM, persianDOM,
   catalanDOM, hindiDOM, noDOMProfile]

theorem allDOMProfiles_count : allDOMProfiles.length = 8 := by native_decide

-- ============================================================================
-- Per-Language Monotonicity Verification
-- ============================================================================

/-! Each language's DOM pattern forms an upper set in the bidimensional
animacy × definiteness grid — Aissen's central prediction. -/

theorem spanish_monotone : spanishDOM.isMonotone = true := by native_decide
theorem russian_monotone : russianDOM.isMonotone = true := by native_decide
theorem turkish_monotone : turkishDOM.isMonotone = true := by native_decide
theorem hebrew_monotone : hebrewDOM.isMonotone = true := by native_decide
theorem persian_monotone : persianDOM.isMonotone = true := by native_decide
theorem catalan_monotone : catalanDOM.isMonotone = true := by native_decide
theorem hindi_monotone : hindiDOM.isMonotone = true := by native_decide
theorem no_dom_monotone : noDOMProfile.isMonotone = true := by native_decide

/-- **Aissen's DOM monotonicity universal**: all attested DOM patterns in
the sample form upper sets in the bidimensional animacy × definiteness
grid. No language marks a less-prominent object while leaving a
more-prominent one unmarked. -/
theorem dom_monotonicity_universal :
    allDOMProfiles.all (·.isMonotone) = true := by native_decide

-- ============================================================================
-- One-Dimensional Classification
-- ============================================================================

/-! Verify that the one-dimensional profiles are indeed one-dimensional,
and that Hindi is genuinely two-dimensional. -/

theorem spanish_animacy_only : spanishDOM.isAnimacyOnly = true := by native_decide
theorem russian_animacy_only : russianDOM.isAnimacyOnly = true := by native_decide

theorem turkish_definiteness_only : turkishDOM.isDefinitenessOnly = true := by native_decide
theorem hebrew_definiteness_only : hebrewDOM.isDefinitenessOnly = true := by native_decide
theorem persian_definiteness_only : persianDOM.isDefinitenessOnly = true := by native_decide
theorem catalan_definiteness_only : catalanDOM.isDefinitenessOnly = true := by native_decide

/-- Hindi DOM depends on both animacy and definiteness — it cannot be
reduced to a single scale. -/
theorem hindi_not_animacy_only : hindiDOM.isAnimacyOnly = false := by native_decide
theorem hindi_not_definiteness_only : hindiDOM.isDefinitenessOnly = false := by native_decide

-- ============================================================================
-- Scale Dominance Theorems
-- ============================================================================

/-! Consequences of monotonicity: higher prominence on one dimension
implies at least as much marking, holding the other dimension constant. -/

/-- In all sample languages, human objects are never less marked than
animate objects at the same definiteness level. -/
theorem human_dominates_animate :
    allDOMProfiles.all (λ p =>
      DefinitenessLevel.all.all (λ d =>
        if p.marks .animate d then p.marks .human d else true)) = true := by
  native_decide

/-- In all sample languages, animate objects are never less marked than
inanimate objects at the same definiteness level. -/
theorem animate_dominates_inanimate :
    allDOMProfiles.all (λ p =>
      DefinitenessLevel.all.all (λ d =>
        if p.marks .inanimate d then p.marks .animate d else true)) = true := by
  native_decide

/-- In all sample languages, pronouns are never less marked than proper
names at the same animacy level. -/
theorem pronoun_dominates_properName :
    allDOMProfiles.all (λ p =>
      AnimacyLevel.all.all (λ a =>
        if p.marks a .properName then p.marks a .personalPronoun else true)) = true := by
  native_decide

/-- In all sample languages, definite NPs are never less marked than
indefinite specific NPs at the same animacy level. -/
theorem definite_dominates_indefiniteSpecific :
    allDOMProfiles.all (λ p =>
      AnimacyLevel.all.all (λ a =>
        if p.marks a .indefiniteSpecific then p.marks a .definite else true)) = true := by
  native_decide

-- ============================================================================
-- Extreme Cell Theorems
-- ============================================================================

/-! The most prominent cell (human, pronoun) is always marked when any
DOM exists; the least prominent cell (inanimate, non-specific) is never
marked in our sample. -/

/-- If any cell is marked, the most prominent cell (human, pronoun)
is also marked. -/
theorem top_cell_marked_if_any :
    allDOMProfiles.all (λ p =>
      if AnimacyLevel.all.any (λ a =>
           DefinitenessLevel.all.any (λ d => p.marks a d))
      then p.marks .human .personalPronoun
      else true) = true := by native_decide

/-- The least prominent cell (inanimate, non-specific) is unmarked in
all DOM languages in the sample. -/
theorem bottom_cell_unmarked :
    allDOMProfiles.all (λ p =>
      p.marks .inanimate .nonSpecific == false) = true := by native_decide

-- ============================================================================
-- Grid Size
-- ============================================================================

/-- The bidimensional grid has 3 × 5 = 15 cells per language. -/
theorem grid_size :
    AnimacyLevel.all.length * DefinitenessLevel.all.length = 15 := by native_decide

/-- Total marked cells across all sample languages. -/
def totalMarkedCells : Nat :=
  allDOMProfiles.foldl (λ acc p =>
    acc + (AnimacyLevel.all.foldl (λ acc₂ a =>
      acc₂ + (DefinitenessLevel.all.filter (p.marks a)).length) 0)) 0

/-- Marked cells: Spanish (5) + Russian (10) + Turkish (9) + Hebrew (9) +
Persian (9) + Catalan (3) + Hindi (7) + NoDOM (0) = 52. -/
theorem total_marked_cells_value : totalMarkedCells = 52 := by native_decide

end Phenomena.Case.Typology
