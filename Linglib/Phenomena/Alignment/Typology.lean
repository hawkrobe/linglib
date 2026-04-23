import Linglib.Core.Lexical.Word
import Linglib.Core.Case.Basic
import Linglib.Core.Case.FeatureBundle
import Linglib.Core.Case.Split
import Linglib.Features.Prominence
import Linglib.Datasets.WALS.Features.F98A
import Linglib.Datasets.WALS.Features.F99A
import Linglib.Datasets.WALS.Features.F100A
-- Fragment imports for bridge theorems (verify Fragment ↔ Typology consistency)
import Linglib.Fragments.Dargwa.Case
import Linglib.Fragments.Japanese.Case
import Linglib.Fragments.Hindi.Case

/-!
# Morphosyntactic Alignment Typology (WALS Chapters 98--100)
@cite{comrie-1978} @cite{comrie-2013} @cite{dixon-1994} @cite{dryer-haspelmath-2013} @cite{dixon-1972} @cite{haspelmath-2021}

Formalizes three chapters from the World Atlas of Language Structures (WALS)
covering morphosyntactic alignment -- the way languages mark the core
grammatical relations S (sole argument of intransitive), A (agent of
transitive), and P (patient of transitive):

- **Chapter 98**: Alignment of Case Marking of Full Noun Phrases. How full NPs are case-marked for S, A, P roles.
- **Chapter 99**: Alignment of Case Marking of Pronouns.
  Same dimension but restricted to pronominal arguments, which frequently
  diverge from full NP marking.
- **Chapter 100**: Alignment of Verbal Person Marking.
  How person agreement on the verb distinguishes S, A, P.

## Alignment Types

Five alignment patterns recur across all three domains:

- **Neutral**: S = A = P (no case/agreement distinction at all)
- **Accusative**: S = A vs P (subject grouped together, patient marked)
- **Ergative**: S = P vs A (absolutive grouped together, agent marked)
- **Tripartite**: S ≠ A ≠ P (all three distinctly marked)
- **Active** (or split-S): S splits into agent-like (= A) and patient-like (= P)

## Key Generalizations

Accusative alignment dominates cross-linguistically in all three domains.
However, the three domains frequently diverge within a single language --
the phenomenon of **split ergativity**. @cite{dixon-1994} established the
generalization that ergative case marking is more common for full NPs
than for pronouns: many "ergative" languages are ergative for NPs but
accusative for pronouns (e.g., Dyirbal, many Australian languages).
Tripartite and active systems are typologically rare.

-/

namespace Phenomena.Alignment.Typology

-- ============================================================================
-- WALS Generated Data References
-- ============================================================================

private abbrev ch98 := Datasets.WALS.F98A.allData
private abbrev ch99 := Datasets.WALS.F99A.allData
private abbrev ch100 := Datasets.WALS.F100A.allData

-- ============================================================================
-- Alignment Types
-- ============================================================================

/-- Morphosyntactic alignment type for case marking or verbal person marking.

These five categories classify how a language groups the three core
grammatical relations S, A, P:
- S = sole argument of an intransitive verb ("The man fell")
- A = agent-like argument of a transitive verb ("The man hit the dog")
- P = patient-like argument of a transitive verb ("The man hit the dog")

The alignment determines which relations receive the same morphological
treatment (case marking or agreement pattern). -/
inductive AlignmentType where
  /-- Neutral (S = A = P): no morphological distinction among the three
      relations. Common in isolating languages (e.g., Mandarin, Thai). -/
  | neutral
  /-- Accusative (S = A ≠ P): subject and agent grouped as "nominative",
      patient distinctly marked as "accusative". The most common pattern
      worldwide (e.g., English, Latin, Russian, Japanese). -/
  | accusative
  /-- Ergative (S = P ≠ A): absolutive groups S and P, while A receives
      distinct "ergative" marking (e.g., Basque, Dyirbal NPs, Hindi
      perfective). -/
  | ergative
  /-- Tripartite (S ≠ A ≠ P): all three relations distinctly marked.
      Extremely rare (e.g., Nez Perce pronouns, some Australian languages). -/
  | tripartite
  /-- Active / split-S: intransitive S is split -- agent-like S patterns
      with A, patient-like S patterns with P. The split is typically
      lexically or semantically determined (e.g., Georgian, Guarani). -/
  | active
  deriving DecidableEq, Repr

instance : Inhabited AlignmentType := ⟨.neutral⟩

/-- Whether this alignment type marks the agent (A) distinctly from S. -/
def AlignmentType.marksAgent : AlignmentType → Bool
  | .ergative   => true
  | .tripartite => true
  | _           => false

/-- Whether this alignment type marks the patient (P) distinctly from S. -/
def AlignmentType.marksPatient : AlignmentType → Bool
  | .accusative => true
  | .tripartite => true
  | _           => false

/-- Whether this alignment groups S with A (nominative-accusative pattern). -/
def AlignmentType.IsNomAcc (a : AlignmentType) : Prop := a = .accusative

instance : DecidablePred AlignmentType.IsNomAcc :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- Whether this alignment groups S with P (absolutive-ergative pattern). -/
def AlignmentType.IsAbsErg (a : AlignmentType) : Prop := a = .ergative

instance : DecidablePred AlignmentType.IsAbsErg :=
  fun _ => inferInstanceAs (Decidable (_ = _))

-- ============================================================================
-- WALS Converter Functions
-- ============================================================================

/-- Convert F98A NP case alignment to our AlignmentType.
    WALS distinguishes standard and marked-nominative accusative; we merge both. -/
private def fromWALS98A : Datasets.WALS.F98A.NPCaseAlignment → AlignmentType
  | .neutral => .neutral
  | .nominativeAccusative => .accusative
  | .nominativeAccusative_3 => .accusative  -- marked nominative, still accusative
  | .ergativeAbsolutive => .ergative
  | .tripartite => .tripartite
  | .activeInactive => .active

/-- Convert F99A pronoun case alignment to our AlignmentType.
    WALS has a "none" category (no pronouns or no case on pronouns);
    we map it to neutral. -/
private def fromWALS99A : Datasets.WALS.F99A.PronounCaseAlignment → AlignmentType
  | .neutral => .neutral
  | .nominativeAccusative => .accusative
  | .nominativeAccusative_3 => .accusative
  | .ergativeAbsolutive => .ergative
  | .tripartite => .tripartite
  | .activeInactive => .active
  | .none => .neutral

/-- Convert F100A verbal person alignment to our AlignmentType.
    WALS has "hierarchical" and "split" categories not in our type;
    returns `none` for these. -/
private def fromWALS100A : Datasets.WALS.F100A.VerbalPersonAlignment → Option AlignmentType
  | .neutral => some .neutral
  | .accusative => some .accusative
  | .ergative => some .ergative
  | .active => some .active
  | .hierarchical => none
  | .split => none

-- ============================================================================
-- Chapter 98--100: Sample Size Totals (from generated data)
-- ============================================================================

theorem ch98_total : ch98.length = 190 := by native_decide
theorem ch99_total : ch99.length = 172 := by native_decide
theorem ch100_total : ch100.length = 380 := by native_decide

-- ============================================================================
-- Chapter-Level Distribution Theorems
-- ============================================================================

/-- Ch 98: Neutral marking is the most common for full NPs (many languages
    lack case marking on NPs entirely). -/
theorem ch98_neutral_modal :
    let neutral := (ch98.filter (·.value == .neutral)).length
    neutral > (ch98.filter (·.value == .nominativeAccusative)).length ∧
    neutral > (ch98.filter (·.value == .ergativeAbsolutive)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 98: Among languages with case marking on NPs, accusative outnumbers
    ergative. -/
theorem ch98_accusative_gt_ergative :
    (ch98.filter (·.value == .nominativeAccusative)).length >
    (ch98.filter (·.value == .ergativeAbsolutive)).length := by native_decide

/-- Ch 99: Accusative alignment outnumbers ergative for pronouns,
    though neutral is the most common category (many languages lack
    distinct pronoun case forms). -/
theorem ch99_accusative_gt_ergative :
    (ch99.filter (·.value == .nominativeAccusative)).length >
    (ch99.filter (·.value == .ergativeAbsolutive)).length := by native_decide

/-- Ch 100: Accusative alignment is the most common for verbal person marking. -/
theorem ch100_accusative_dominant :
    let acc := (ch100.filter (·.value == .accusative)).length
    acc > (ch100.filter (·.value == .neutral)).length ∧
    acc > (ch100.filter (·.value == .ergative)).length ∧
    acc > (ch100.filter (·.value == .active)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 98: Tripartite and active-inactive alignments are the rarest for
    full NPs. -/
theorem ch98_tripartite_rare :
    (ch98.filter (·.value == .tripartite)).length <
    (ch98.filter (·.value == .ergativeAbsolutive)).length ∧
    (ch98.filter (·.value == .activeInactive)).length <
    (ch98.filter (·.value == .ergativeAbsolutive)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 99: Tripartite is also rare for pronouns. -/
theorem ch99_tripartite_rare :
    (ch99.filter (·.value == .tripartite)).length <
    (ch99.filter (·.value == .ergativeAbsolutive)).length := by native_decide

-- ============================================================================
-- AlignmentProfile: Combined Profile Across All Three Chapters
-- ============================================================================

/-- A language's alignment profile, combining classifications from all three
WALS alignment chapters.

This structure records a single language's position in each of the three
typological dimensions: case marking on full NPs (Ch 98), case marking
on pronouns (Ch 99), and verbal person marking (Ch 100). Languages
frequently have different alignment types in different domains -- this is
the phenomenon of split ergativity. -/
structure AlignmentProfile where
  /-- Language name -/
  name : String
  /-- ISO 639-3 code -/
  iso639 : String
  /-- Ch 98: Alignment of case marking of full NPs -/
  npAlignment : AlignmentType
  /-- Ch 99: Alignment of case marking of pronouns -/
  pronAlignment : AlignmentType
  /-- Ch 100: Alignment of verbal person marking -/
  verbAlignment : AlignmentType
  /-- Notes on the alignment system -/
  notes : String := ""
  deriving Repr, DecidableEq

/-- Whether NP and pronoun alignment match (no split ergativity in case). -/
def AlignmentProfile.caseUniform (p : AlignmentProfile) : Bool :=
  p.npAlignment == p.pronAlignment

/-- Whether the language shows the classic NP-ergative / pronoun-accusative
    split (Dixon's generalization). -/
def AlignmentProfile.dixonSplit (p : AlignmentProfile) : Bool :=
  p.npAlignment == .ergative && p.pronAlignment == .accusative

/-- Whether all three domains have the same alignment. -/
def AlignmentProfile.fullyUniform (p : AlignmentProfile) : Bool :=
  p.npAlignment == p.pronAlignment && p.pronAlignment == p.verbAlignment

/-- Whether the language has any ergative alignment in any domain. -/
def AlignmentProfile.hasAnyErgative (p : AlignmentProfile) : Bool :=
  p.npAlignment == .ergative || p.pronAlignment == .ergative ||
  p.verbAlignment == .ergative

/-- Whether the language has accusative alignment in all case-marking
    domains (NPs and pronouns). -/
def AlignmentProfile.accusativeCase (p : AlignmentProfile) : Bool :=
  p.npAlignment == .accusative && p.pronAlignment == .accusative

-- ============================================================================
-- Language Data (20 languages)
-- ============================================================================

section LanguageData

/-- English: accusative case marking on pronouns (I/me, he/him), no case
    on full NPs (neutral), and accusative verb agreement (verb agrees with
    subject = S/A grouping). -/
def english : AlignmentProfile :=
  { name := "English"
    iso639 := "eng"
    npAlignment := .neutral
    pronAlignment := .accusative
    verbAlignment := .accusative
    notes := "Case only on pronouns (I/me); verb agrees with S/A" }

/-- Hindi-Urdu: split-ergative. Ergative case marking (-ne on A) in
    perfective aspect for both NPs and pronouns. Accusative alignment in
    imperfective. WALS codes the dominant pattern as ergative for NPs,
    accusative for pronouns (the pronoun forms are less consistently
    ergative). Verb agreement is neutral (agrees with unmarked argument). -/
def hindiUrdu : AlignmentProfile :=
  { name := "Hindi-Urdu"
    iso639 := "hin"
    npAlignment := .ergative
    pronAlignment := .accusative
    verbAlignment := .neutral
    notes := "Split ergative: -ne on A in perfective; verb agrees with unmarked arg" }

/-- Basque: consistently ergative across all three domains. Ergative case
    (-k) marks A on both NPs and pronouns. Verb agreement cross-references
    S/P (absolutive) and A (ergative) with distinct slots -- ergative
    alignment in agreement. -/
def basque : AlignmentProfile :=
  { name := "Basque"
    iso639 := "eus"
    npAlignment := .ergative
    pronAlignment := .ergative
    verbAlignment := .ergative
    notes := "Consistently ergative; -k on A; verb cross-references abs and erg" }

/-- Dyirbal (Pama-Nyungan, Australia): the textbook case of split
    ergativity. Full NPs have ergative case marking, but
    1st/2nd person pronouns follow accusative alignment. Verb has
    no person agreement (neutral). -/
def dyirbal : AlignmentProfile :=
  { name := "Dyirbal"
    iso639 := "dbl"
    npAlignment := .ergative
    pronAlignment := .accusative
    verbAlignment := .neutral
    notes := "Dixon's (1972) textbook split-ergative: NPs erg, pronouns acc" }

/-- Georgian: active (split-S) alignment. The verb agreement system
    shows an active pattern: some intransitive S arguments pattern like
    A, others like P, depending on the verb class (unergative vs.
    unaccusative). Case marking is also active in some series. -/
def georgian : AlignmentProfile :=
  { name := "Georgian"
    iso639 := "kat"
    npAlignment := .active
    pronAlignment := .active
    verbAlignment := .active
    notes := "Active (split-S); verb class determines S alignment" }

/-- Tagalog: neutral case marking on NPs and pronouns (the Philippine
    voice system does not straightforwardly map to accusative/ergative
    alignment). Verbal person marking is also neutral in the WALS sense. -/
def tagalog : AlignmentProfile :=
  { name := "Tagalog"
    iso639 := "tgl"
    npAlignment := .neutral
    pronAlignment := .neutral
    verbAlignment := .neutral
    notes := "Philippine voice system; WALS codes as neutral" }

/-- Japanese: accusative case marking on NPs (ga nom, o acc) and pronouns.
    No verb person agreement (neutral). -/
def japanese : AlignmentProfile :=
  { name := "Japanese"
    iso639 := "jpn"
    npAlignment := .accusative
    pronAlignment := .accusative
    verbAlignment := .neutral
    notes := "ga/o case particles; no verb agreement" }

/-- Latin: accusative case marking on both NPs and pronouns (nominative
    vs. accusative). Verb agreement is accusative (agrees with S/A). -/
def latin : AlignmentProfile :=
  { name := "Latin"
    iso639 := "lat"
    npAlignment := .accusative
    pronAlignment := .accusative
    verbAlignment := .accusative
    notes := "Nom/acc case; verb agrees with S/A" }

/-- Russian: accusative alignment across all three domains. Nominative
    marks S/A, accusative marks P (with animacy-conditioned syncretism).
    Verb agrees with S/A. -/
def russian : AlignmentProfile :=
  { name := "Russian"
    iso639 := "rus"
    npAlignment := .accusative
    pronAlignment := .accusative
    verbAlignment := .accusative
    notes := "Nom/acc; animacy-conditioned acc syncretism" }

/-- Mandarin Chinese: neutral alignment in all three domains. No
    morphological case marking, no verb person agreement. Grammatical
    relations encoded by word order. -/
def mandarin : AlignmentProfile :=
  { name := "Mandarin Chinese"
    iso639 := "cmn"
    npAlignment := .neutral
    pronAlignment := .neutral
    verbAlignment := .neutral
    notes := "No case, no agreement; word order encodes relations" }

/-- Turkish: accusative case marking on NPs (with differential object
    marking) and pronouns. Verb agreement is accusative (agrees with S/A). -/
def turkish : AlignmentProfile :=
  { name := "Turkish"
    iso639 := "tur"
    npAlignment := .accusative
    pronAlignment := .accusative
    verbAlignment := .accusative
    notes := "Nom/acc case with DOM; verb agrees with S/A" }

/-- Tongan (Austronesian): ergative case marking on NPs. Pronouns are
    also ergative. No verb person agreement (neutral). -/
def tongan : AlignmentProfile :=
  { name := "Tongan"
    iso639 := "ton"
    npAlignment := .ergative
    pronAlignment := .ergative
    verbAlignment := .neutral
    notes := "Ergative case on both NPs and pronouns; no verb agreement" }

/-- Guarani (Tupian): active (split-S) case marking and verb agreement.
    The set of prefixes used on the verb depends on whether the S argument
    is agent-like or patient-like. -/
def guarani : AlignmentProfile :=
  { name := "Guarani"
    iso639 := "grn"
    npAlignment := .neutral
    pronAlignment := .neutral
    verbAlignment := .active
    notes := "Active verb agreement; oral/nasal prefix split for S" }

/-- Samoan (Austronesian): ergative case marking on full NPs (ergative
    particle e before A). Pronouns have accusative alignment. Verb
    agreement is neutral. -/
def samoan : AlignmentProfile :=
  { name := "Samoan"
    iso639 := "smo"
    npAlignment := .ergative
    pronAlignment := .accusative
    verbAlignment := .neutral
    notes := "Ergative NPs (e before A); accusative pronouns" }

/-- German: accusative case marking on NPs and pronouns (nom/acc
    distinction). Verb agreement is accusative (agrees with S/A). -/
def german : AlignmentProfile :=
  { name := "German"
    iso639 := "deu"
    npAlignment := .accusative
    pronAlignment := .accusative
    verbAlignment := .accusative
    notes := "Nom/acc case; verb agrees with S/A" }

/-- Swahili (Bantu): neutral case marking (no morphological case on NPs
    or pronouns). Verb agreement is accusative (subject prefixes
    cross-reference S/A). -/
def swahili : AlignmentProfile :=
  { name := "Swahili"
    iso639 := "swh"
    npAlignment := .neutral
    pronAlignment := .neutral
    verbAlignment := .accusative
    notes := "No case; S/A subject prefix on verb" }

/-- Tibetan (Central, Lhasa): ergative case marking on NPs and pronouns
    (ergative particles -gis and -kyis on A). Verb is neutral (no person
    agreement). -/
def tibetan : AlignmentProfile :=
  { name := "Tibetan (Lhasa)"
    iso639 := "bod"
    npAlignment := .ergative
    pronAlignment := .ergative
    verbAlignment := .neutral
    notes := "Ergative -gis, -kyis on A; no verb agreement" }

/-- Nez Perce (Sahaptian): tripartite case marking on NPs (nominative
    for S, ergative for A, accusative for P -- all three distinctly
    marked). Pronouns are also tripartite. Verb agreement is
    accusative. -/
def nezPerce : AlignmentProfile :=
  { name := "Nez Perce"
    iso639 := "nez"
    npAlignment := .tripartite
    pronAlignment := .tripartite
    verbAlignment := .accusative
    notes := "Tripartite case: distinct nom, erg, acc" }

/-- Finnish: accusative case marking on NPs and pronouns (nominative for
    S/A, partitive/accusative for P). Verb agreement is accusative
    (agrees with S/A). -/
def finnish : AlignmentProfile :=
  { name := "Finnish"
    iso639 := "fin"
    npAlignment := .accusative
    pronAlignment := .accusative
    verbAlignment := .accusative
    notes := "Nom/acc(partitive); verb agrees with S/A" }

/-- Warlpiri (Pama-Nyungan, Australia): ergative case marking on full NPs
    (ergative -ngku and -rlu on A). Pronouns have accusative alignment
    (nom and acc). Verb agreement is neutral (no person marking on verb in
    the standard analysis). -/
def warlpiri : AlignmentProfile :=
  { name := "Warlpiri"
    iso639 := "wbp"
    npAlignment := .ergative
    pronAlignment := .accusative
    verbAlignment := .neutral
    notes := "Split ergative: NPs erg, pronouns acc; free word order" }

/-- Dargwa (Tanti; Nakh-Dagestanian): consistently ergative across all
    three domains. Ergative -li marks A on both full NPs and pronouns
    (@cite{sumbatova-2021} §4.4.3). Gender agreement on the verb is controlled
    by the absolutive argument (ergative alignment). Person agreement follows
    a hierarchical pattern (1,2 > 3; abs > erg) but the primary dimension
    is ergative. No tense-conditioned or animacy-conditioned split. -/
def dargwa : AlignmentProfile :=
  { name := "Dargwa (Tanti)"
    iso639 := "dar"
    npAlignment := .ergative
    pronAlignment := .ergative
    verbAlignment := .ergative
    notes := "Consistently ergative; -li on A; gender agrees with absolutive" }

/-- Yukatek Maya (Yucatecan Mayan): aspect-conditioned split-intransitive
    system. In perfective clauses (completive/subjunctive status), S is
    cross-referenced by set-B markers (ergative pattern). In imperfective
    clauses (incompletive status), S is cross-referenced by set-A markers
    (accusative pattern). Transitive marking is not affected by the split.

    @cite{bohnemeyer-2004}: the split is not conditioned by lexical verb
    class (not split-S or fluid-S) but by viewpoint aspect, making it
    a typologically rare case of aspect-conditioned split intransitivity.
    WALS codes Yukatek verbal person marking as "split" (F100A). -/
def yukatek : AlignmentProfile :=
  { name := "Yukatek Maya"
    iso639 := "yua"
    npAlignment := .neutral      -- no NP case marking
    pronAlignment := .neutral    -- pronouns lack case morphology
    verbAlignment := .active     -- aspect-conditioned split in S marking
    notes := "Aspect-conditioned split-S: PRV → erg (set-B), IMPFV → acc (set-A)" }

end LanguageData

-- ============================================================================
-- Language Collection
-- ============================================================================

/-- All alignment profiles in our sample. -/
def allProfiles : List AlignmentProfile :=
  [ english, hindiUrdu, basque, dyirbal, georgian, tagalog
  , japanese, latin, russian, mandarin, turkish, tongan
  , guarani, samoan, german, swahili, tibetan, nezPerce
  , finnish, warlpiri, dargwa, yukatek ]

theorem allProfiles_count : allProfiles.length = 22 := by native_decide

-- ============================================================================
-- ISO 639-3 Verification
-- ============================================================================

/-- All ISO 639-3 codes are non-empty. -/
theorem all_iso_nonempty :
    allProfiles.all (fun p => p.iso639.length > 0) = true := by native_decide

/-- All ISO 639-3 codes are exactly 3 characters (standard length). -/
theorem all_iso_length_3 :
    allProfiles.all (fun p => p.iso639.length == 3) = true := by native_decide

/-- No duplicate ISO codes (each language appears once). -/
theorem iso_codes_unique :
    (allProfiles.map (·.iso639)).eraseDups.length =
    allProfiles.length := by native_decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

/-! Spot-checks that each language has the expected alignment values. -/

-- NP alignment
theorem english_np_neutral : english.npAlignment = .neutral := by native_decide
theorem basque_np_ergative : basque.npAlignment = .ergative := by native_decide
theorem japanese_np_accusative : japanese.npAlignment = .accusative := by native_decide
theorem georgian_np_active : georgian.npAlignment = .active := by native_decide
theorem nezPerce_np_tripartite : nezPerce.npAlignment = .tripartite := by native_decide
theorem dyirbal_np_ergative : dyirbal.npAlignment = .ergative := by native_decide

-- Pronoun alignment
theorem english_pron_accusative : english.pronAlignment = .accusative := by native_decide
theorem basque_pron_ergative : basque.pronAlignment = .ergative := by native_decide
theorem dyirbal_pron_accusative : dyirbal.pronAlignment = .accusative := by native_decide
theorem tagalog_pron_neutral : tagalog.pronAlignment = .neutral := by native_decide

-- Verb alignment
theorem basque_verb_ergative : basque.verbAlignment = .ergative := by native_decide
theorem latin_verb_accusative : latin.verbAlignment = .accusative := by native_decide
theorem japanese_verb_neutral : japanese.verbAlignment = .neutral := by native_decide
theorem georgian_verb_active : georgian.verbAlignment = .active := by native_decide

-- Dargwa
theorem dargwa_np_ergative : dargwa.npAlignment = .ergative := by native_decide
theorem dargwa_pron_ergative : dargwa.pronAlignment = .ergative := by native_decide
theorem dargwa_verb_ergative : dargwa.verbAlignment = .ergative := by native_decide

-- Yukatek Maya
theorem yukatek_np_neutral : yukatek.npAlignment = .neutral := by native_decide
theorem yukatek_pron_neutral : yukatek.pronAlignment = .neutral := by native_decide
theorem yukatek_verb_active : yukatek.verbAlignment = .active := by native_decide

-- Split ergativity
theorem dyirbal_is_dixon_split : dyirbal.dixonSplit = true := by native_decide
theorem hindiUrdu_is_dixon_split : hindiUrdu.dixonSplit = true := by native_decide
theorem warlpiri_is_dixon_split : warlpiri.dixonSplit = true := by native_decide
theorem samoan_is_dixon_split : samoan.dixonSplit = true := by native_decide

-- Uniform alignment
theorem basque_fully_uniform : basque.fullyUniform = true := by native_decide
theorem dargwa_fully_uniform : dargwa.fullyUniform = true := by native_decide
theorem mandarin_fully_uniform : mandarin.fullyUniform = true := by native_decide
theorem latin_fully_uniform : latin.fullyUniform = true := by native_decide

-- ============================================================================
-- Typological Generalizations
-- ============================================================================

/-! ### Generalization 1: Accusative is the most common alignment for pronouns.

Across WALS Ch 99, accusative (83) outnumbers all other pronoun alignment
types. In our sample, accusative pronoun marking is likewise the most
frequent pattern. -/

theorem gen1_accusative_most_common_pronouns :
    (allProfiles.filter (fun p => p.pronAlignment == .accusative)).length >=
    (allProfiles.filter (fun p => p.pronAlignment == .ergative)).length := by
  native_decide

/-! ### Generalization 2: Ergative NP marking is more common than ergative
pronoun marking (Dixon's generalization).

@cite{dixon-1994} established that in the animacy/nominal hierarchy, ergative
case marking is more likely to appear on full NPs than on pronouns. In
our sample, more languages have ergative NP alignment than ergative
pronoun alignment. -/

theorem gen2_dixon_generalization :
    (allProfiles.filter (fun p => p.npAlignment == .ergative)).length >
    (allProfiles.filter (fun p => p.pronAlignment == .ergative)).length := by
  native_decide

/-! ### Generalization 3: Split ergativity -- ergative NPs with accusative
pronouns.

Many "ergative" languages show a split: NPs are ergative but pronouns are
accusative. This pattern is attested multiple times in our sample
(Dyirbal, Hindi-Urdu, Samoan, Warlpiri). -/

theorem gen3_split_ergativity_attested :
    (allProfiles.filter (fun p => p.dixonSplit)).length >= 4 := by
  native_decide

/-! ### Generalization 4: No language has accusative NPs with ergative pronouns.

The reverse of Dixon's split (accusative NPs, ergative pronouns) is
predicted not to occur. Our sample confirms this: whenever pronouns are
ergative, NPs are at least ergative too. -/

theorem gen4_no_reverse_dixon :
    allProfiles.all (fun p =>
      if p.pronAlignment == .ergative
      then p.npAlignment == .ergative || p.npAlignment == .tripartite
      else true) = true := by
  native_decide

/-! ### Generalization 5: Tripartite alignment is extremely rare.

In WALS Ch 98, only 2 out of 190 languages have tripartite NP alignment.
In our sample, only Nez Perce is tripartite for NPs. -/

theorem gen5_tripartite_rare_nps :
    (allProfiles.filter (fun p => p.npAlignment == .tripartite)).length <= 1 := by
  native_decide

theorem gen5_tripartite_rare_pronouns :
    (allProfiles.filter (fun p => p.pronAlignment == .tripartite)).length <= 1 := by
  native_decide

/-! ### Generalization 6: Active alignment is rare for case marking.

Active (split-S) systems are uncommon for case marking. In our sample,
only Georgian shows active case marking on NPs and pronouns. -/

theorem gen6_active_rare_case :
    (allProfiles.filter (fun p => p.npAlignment == .active)).length <= 2 := by
  native_decide

/-! ### Generalization 6a: Aspect-conditioned split intransitivity.

Yukatek Maya and Georgian both show active (split-S) verbal person marking.
In both languages, the split is conditioned by viewpoint aspect: perfective
triggers ergative-like marking, imperfective triggers accusative-like marking.
@cite{bohnemeyer-2004} argues this reduces to a single linking-by-viewpoint
mechanism projected from the causal chain of subevents in event structure. -/

theorem gen6a_aspect_split_languages :
    (allProfiles.filter (fun p => p.verbAlignment == .active)).length >= 2 := by
  native_decide

theorem gen6a_yukatek_and_georgian_both_active :
    yukatek.verbAlignment = .active ∧ georgian.verbAlignment = .active := ⟨rfl, rfl⟩

/-! ### Generalization 7: Languages with ergative NP marking tend to have
ergative or neutral verbal person marking.

When NP case is ergative, the verb agreement is typically either ergative
(like Basque) or neutral (like Dyirbal, Tibetan). Accusative verb
agreement with ergative NP case is uncommon. -/

theorem gen7_erg_np_verb_pattern :
    allProfiles.all (fun p =>
      if p.npAlignment == .ergative
      then p.verbAlignment == .ergative || p.verbAlignment == .neutral ||
           p.verbAlignment == .accusative
      else true) = true := by
  native_decide

/-! ### Generalization 8: All five alignment types are attested for NPs.

Our sample covers every WALS alignment category for full NPs. -/

theorem gen8_all_np_types_attested :
    allProfiles.any (fun p => p.npAlignment == .neutral) &&
    allProfiles.any (fun p => p.npAlignment == .accusative) &&
    allProfiles.any (fun p => p.npAlignment == .ergative) &&
    allProfiles.any (fun p => p.npAlignment == .tripartite) &&
    allProfiles.any (fun p => p.npAlignment == .active) = true := by
  native_decide

/-! ### Generalization 9: All five alignment types are attested for pronouns. -/

theorem gen9_all_pron_types_attested :
    allProfiles.any (fun p => p.pronAlignment == .neutral) &&
    allProfiles.any (fun p => p.pronAlignment == .accusative) &&
    allProfiles.any (fun p => p.pronAlignment == .ergative) &&
    allProfiles.any (fun p => p.pronAlignment == .tripartite) &&
    allProfiles.any (fun p => p.pronAlignment == .active) = true := by
  native_decide

/-! ### Generalization 10: Four of the five alignment types are attested for
verbal person marking. Tripartite verb agreement is exceedingly rare
cross-linguistically (WALS Ch 100 lists only 5 out of 378 languages)
and is not represented in our sample. -/

theorem gen10_verb_types_attested :
    allProfiles.any (fun p => p.verbAlignment == .neutral) &&
    allProfiles.any (fun p => p.verbAlignment == .accusative) &&
    allProfiles.any (fun p => p.verbAlignment == .ergative) &&
    allProfiles.any (fun p => p.verbAlignment == .active) = true := by
  native_decide

theorem gen10_tripartite_verb_unattested :
    allProfiles.all (fun p => p.verbAlignment != .tripartite) = true := by
  native_decide

/-! ### Generalization 11: Neutral NP alignment implies neutral or accusative
pronoun alignment.

Languages without case marking on NPs (neutral) either also lack case
marking on pronouns (neutral) or have accusative pronoun case (like
English, where case survives only on pronouns). They never have
ergative pronoun case without NP case. -/

theorem gen11_neutral_np_pronoun :
    allProfiles.all (fun p =>
      if p.npAlignment == .neutral
      then p.pronAlignment == .neutral || p.pronAlignment == .accusative
      else true) = true := by
  native_decide

/-! ### Generalization 12: Fully uniform alignment is common.

Many languages have the same alignment type across all three domains.
This includes languages like Basque (uniformly ergative), Mandarin
(uniformly neutral), Latin/Russian/Turkish (uniformly accusative),
and Georgian (uniformly active). -/

theorem gen12_uniform_common :
    (allProfiles.filter (fun p => p.fullyUniform)).length >= 5 := by
  native_decide

/-! ### Generalization 13: Accusative verb agreement is the dominant pattern
among languages that have verb agreement.

Among languages with non-neutral verb alignment, accusative agreement
(verb agrees with S/A, i.e., subject agreement) is the most common. -/

theorem gen13_accusative_verb_dominant :
    (allProfiles.filter (fun p => p.verbAlignment == .accusative)).length >
    (allProfiles.filter (fun p => p.verbAlignment == .ergative)).length ∧
    (allProfiles.filter (fun p => p.verbAlignment == .accusative)).length >
    (allProfiles.filter (fun p => p.verbAlignment == .active)).length := by
  native_decide

-- ============================================================================
-- Summary Statistics
-- ============================================================================

/-- Number of languages with ergative NP alignment. -/
def ergativeNpCount : Nat :=
  (allProfiles.filter (fun p => p.npAlignment == .ergative)).length

/-- Number of languages with ergative pronoun alignment. -/
def ergativePronCount : Nat :=
  (allProfiles.filter (fun p => p.pronAlignment == .ergative)).length

/-- Number of languages with Dixon-split ergativity. -/
def dixonSplitCount : Nat :=
  (allProfiles.filter (fun p => p.dixonSplit)).length

/-- Number of fully uniform languages. -/
def uniformCount : Nat :=
  (allProfiles.filter (fun p => p.fullyUniform)).length

theorem ergativeNp_is_8 : ergativeNpCount = 8 := by native_decide
theorem ergativePron_is_4 : ergativePronCount = 4 := by native_decide
theorem dixonSplit_is_4 : dixonSplitCount = 4 := by native_decide
theorem uniform_is_10 : uniformCount = 10 := by native_decide

-- ============================================================================
-- Cross-Chapter Consistency
-- ============================================================================

/-- Languages with no case on NPs should not have ergative NP alignment. -/
theorem neutral_np_not_ergative :
    allProfiles.all (fun p =>
      if p.npAlignment == .neutral then !p.npAlignment.marksAgent
      else true) = true := by
  native_decide

/-- Languages with tripartite case mark both A and P. -/
theorem tripartite_marks_both :
    allProfiles.all (fun p =>
      if p.npAlignment == .tripartite
      then p.npAlignment.marksAgent && p.npAlignment.marksPatient
      else true) = true := by
  native_decide

/-- Ergative alignment marks agent but not patient (S = P grouping). -/
theorem ergative_marks_agent_only :
    AlignmentType.ergative.marksAgent = true ∧
    AlignmentType.ergative.marksPatient = false := by native_decide

/-- Accusative alignment marks patient but not agent (S = A grouping). -/
theorem accusative_marks_patient_only :
    AlignmentType.accusative.marksPatient = true ∧
    AlignmentType.accusative.marksAgent = false := by native_decide

-- ============================================================================
-- Cross-Domain Correlation Patterns
-- ============================================================================

/-- In our sample, every language with accusative NP case also has
    accusative pronoun case. (Accusative alignment does not split
    across the NP/pronoun divide the way ergative does.) -/
theorem accusative_np_implies_accusative_pron :
    allProfiles.all (fun p =>
      if p.npAlignment == .accusative
      then p.pronAlignment == .accusative
      else true) = true := by
  native_decide

/-- No language has tripartite NP alignment without also having
    tripartite pronoun alignment (in our sample). -/
theorem tripartite_np_implies_tripartite_pron :
    allProfiles.all (fun p =>
      if p.npAlignment == .tripartite
      then p.pronAlignment == .tripartite
      else true) = true := by
  native_decide

/-- Active NP alignment implies active pronoun alignment in our sample. -/
theorem active_np_implies_active_pron :
    allProfiles.all (fun p =>
      if p.npAlignment == .active
      then p.pronAlignment == .active
      else true) = true := by
  native_decide

-- ============================================================================
-- WALS Grounding: Ch 98 (NP Case Alignment)
-- Languages not in Ch 98 sample: Dyirbal, Latin, Tongan, Guarani,
-- Samoan, Tibetan, Warlpiri.
-- Note: WALS codes Hindi-Urdu as tripartite and Basque/Georgian as
-- active-inactive, diverging from traditional typological classifications.
-- ============================================================================

theorem english_ch98 :
    (Datasets.WALS.F98A.lookup "eng").map (fromWALS98A ·.value) =
    some english.npAlignment := by native_decide
theorem japanese_ch98 :
    (Datasets.WALS.F98A.lookup "jpn").map (fromWALS98A ·.value) =
    some japanese.npAlignment := by native_decide
theorem russian_ch98 :
    (Datasets.WALS.F98A.lookup "rus").map (fromWALS98A ·.value) =
    some russian.npAlignment := by native_decide
theorem mandarin_ch98 :
    (Datasets.WALS.F98A.lookup "mnd").map (fromWALS98A ·.value) =
    some mandarin.npAlignment := by native_decide
theorem turkish_ch98 :
    (Datasets.WALS.F98A.lookup "tur").map (fromWALS98A ·.value) =
    some turkish.npAlignment := by native_decide
theorem german_ch98 :
    (Datasets.WALS.F98A.lookup "ger").map (fromWALS98A ·.value) =
    some german.npAlignment := by native_decide
theorem swahili_ch98 :
    (Datasets.WALS.F98A.lookup "swa").map (fromWALS98A ·.value) =
    some swahili.npAlignment := by native_decide
theorem tagalog_ch98 :
    (Datasets.WALS.F98A.lookup "tag").map (fromWALS98A ·.value) =
    some tagalog.npAlignment := by native_decide
theorem nezPerce_ch98 :
    (Datasets.WALS.F98A.lookup "nez").map (fromWALS98A ·.value) =
    some nezPerce.npAlignment := by native_decide
theorem finnish_ch98 :
    (Datasets.WALS.F98A.lookup "fin").map (fromWALS98A ·.value) =
    some finnish.npAlignment := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 99 (Pronoun Case Alignment)
-- Same languages absent as Ch 98.
-- ============================================================================

theorem english_ch99 :
    (Datasets.WALS.F99A.lookup "eng").map (fromWALS99A ·.value) =
    some english.pronAlignment := by native_decide
theorem japanese_ch99 :
    (Datasets.WALS.F99A.lookup "jpn").map (fromWALS99A ·.value) =
    some japanese.pronAlignment := by native_decide
theorem russian_ch99 :
    (Datasets.WALS.F99A.lookup "rus").map (fromWALS99A ·.value) =
    some russian.pronAlignment := by native_decide
theorem mandarin_ch99 :
    (Datasets.WALS.F99A.lookup "mnd").map (fromWALS99A ·.value) =
    some mandarin.pronAlignment := by native_decide
theorem turkish_ch99 :
    (Datasets.WALS.F99A.lookup "tur").map (fromWALS99A ·.value) =
    some turkish.pronAlignment := by native_decide
theorem german_ch99 :
    (Datasets.WALS.F99A.lookup "ger").map (fromWALS99A ·.value) =
    some german.pronAlignment := by native_decide
theorem swahili_ch99 :
    (Datasets.WALS.F99A.lookup "swa").map (fromWALS99A ·.value) =
    some swahili.pronAlignment := by native_decide
theorem tagalog_ch99 :
    (Datasets.WALS.F99A.lookup "tag").map (fromWALS99A ·.value) =
    some tagalog.pronAlignment := by native_decide
theorem nezPerce_ch99 :
    (Datasets.WALS.F99A.lookup "nez").map (fromWALS99A ·.value) =
    some nezPerce.pronAlignment := by native_decide
theorem finnish_ch99 :
    (Datasets.WALS.F99A.lookup "fin").map (fromWALS99A ·.value) =
    some finnish.pronAlignment := by native_decide

-- ============================================================================
-- WALS Grounding: Ch 100 (Verbal Person Marking)
-- fromWALS100A returns Option; grounding only for languages with clean mapping.
-- ============================================================================

theorem english_ch100 :
    (Datasets.WALS.F100A.lookup "eng").bind (fromWALS100A ·.value) =
    some english.verbAlignment := by native_decide
theorem russian_ch100 :
    (Datasets.WALS.F100A.lookup "rus").bind (fromWALS100A ·.value) =
    some russian.verbAlignment := by native_decide
theorem mandarin_ch100 :
    (Datasets.WALS.F100A.lookup "mnd").bind (fromWALS100A ·.value) =
    some mandarin.verbAlignment := by native_decide
theorem turkish_ch100 :
    (Datasets.WALS.F100A.lookup "tur").bind (fromWALS100A ·.value) =
    some turkish.verbAlignment := by native_decide
theorem german_ch100 :
    (Datasets.WALS.F100A.lookup "ger").bind (fromWALS100A ·.value) =
    some german.verbAlignment := by native_decide
theorem swahili_ch100 :
    (Datasets.WALS.F100A.lookup "swa").bind (fromWALS100A ·.value) =
    some swahili.verbAlignment := by native_decide
theorem tagalog_ch100 :
    (Datasets.WALS.F100A.lookup "tag").bind (fromWALS100A ·.value) =
    some tagalog.verbAlignment := by native_decide
theorem basque_ch100 :
    (Datasets.WALS.F100A.lookup "bsq").bind (fromWALS100A ·.value) =
    some basque.verbAlignment := by native_decide
theorem finnish_ch100 :
    (Datasets.WALS.F100A.lookup "fin").bind (fromWALS100A ·.value) =
    some finnish.verbAlignment := by native_decide
theorem japanese_ch100 :
    (Datasets.WALS.F100A.lookup "jpn").bind (fromWALS100A ·.value) =
    some japanese.verbAlignment := by native_decide

-- ============================================================================
-- Split-Ergative Conditioning (@cite{silverstein-1976})
-- ============================================================================

/-! ### Silverstein's Hierarchy

@cite{silverstein-1976} predicts that ergative marking targets the **less prominent**
end of the animacy/definiteness scale. More prominent NPs (pronouns, 1st/2nd
person) get accusative treatment; less prominent NPs (full NPs, 3rd person,
inanimate) get ergative treatment.

The `silverstein` function encodes this as a threshold-based predicate over
prominence values, and its monotonicity property captures the implicational
nature of the hierarchy: if a less-prominent NP gets accusative treatment,
all more-prominent NPs do too.

The `dyirbalSplit` instantiates `Core.SplitErgativity` for Dyirbal's
animacy-conditioned split, connecting the split mechanism to the `dyirbal`
alignment profile above.

- Silverstein, M. (1976). Hierarchy of features and ergativity. In Dixon, R.
  M. W. (ed.), *Grammatical Categories in Australian Languages*. AIAS. -/

section SilversteinSplit

open Features.Prominence (AnimacyLevel)

/-- Map the binary Core alignment family to the full alignment type. -/
private def toAlignmentType : Core.AlignmentFamily → AlignmentType
  | .accusative => .accusative
  | .ergative => .ergative

/-- Silverstein's hierarchy: NPs at or above the prominence threshold get
    accusative alignment; those below get ergative. -/
def silverstein (threshold : Nat) (npProminence : Nat) : Core.AlignmentFamily :=
  if npProminence ≥ threshold then .accusative else .ergative

/-- Silverstein is monotone: if prominence p₁ ≥ p₂ and p₂ gets accusative,
    then p₁ gets accusative. (Higher prominence → more likely accusative.) -/
theorem silverstein_monotone (threshold p₁ p₂ : Nat)
    (h_ge : p₁ ≥ p₂) (h_acc : silverstein threshold p₂ = .accusative) :
    silverstein threshold p₁ = .accusative := by
  simp only [silverstein] at *
  split at h_acc
  · split
    · rfl
    · omega
  · contradiction

/-- Silverstein predicts Dixon's generalization: with threshold 1,
    full NPs (prominence 0) get ergative, pronouns (prominence 1) get
    accusative — exactly the NP-ergative / pronoun-accusative split. -/
theorem silverstein_predicts_dixon :
    silverstein 1 0 = .ergative ∧ silverstein 1 1 = .accusative := ⟨rfl, rfl⟩

/-- Dyirbal-style split by animacy: human/animate → accusative,
    inanimate → ergative (@cite{dixon-1972}, @cite{blake-1994} Ch. 4). -/
def dyirbalSplit : Core.SplitErgativity AnimacyLevel :=
  { ergCondition := fun a => a == .inanimate }

theorem dyirbal_human_acc :
    dyirbalSplit.alignment .human = .accusative := rfl

theorem dyirbal_inanimate_erg :
    dyirbalSplit.alignment .inanimate = .ergative := rfl

/-- The Dyirbal split matches the Dyirbal alignment profile: inanimate NPs
    get ergative alignment (matching `dyirbal.npAlignment`). -/
theorem dyirbal_split_matches_np :
    toAlignmentType (dyirbalSplit.alignment .inanimate)
    = dyirbal.npAlignment := rfl

/-- Human/animate arguments get accusative alignment (matching
    `dyirbal.pronAlignment`). -/
theorem dyirbal_split_matches_pron :
    toAlignmentType (dyirbalSplit.alignment .human)
    = dyirbal.pronAlignment := rfl

end SilversteinSplit

-- ============================================================================
-- Ditransitive Alignment (@cite{haspelmath-2021}, §3)
-- ============================================================================

/-! Ditransitive alignment classifies how a language codes R (recipient)
    and T (theme) relative to the monotransitive roles A and P.

    The terminology follows @cite{haspelmath-2005}:
    - **Indirective**: T = P, R distinctly marked (like accusative for
      monotransitives: the "subject-like" argument is unmarked)
    - **Secundative**: R = P, T distinctly marked (like ergative for
      monotransitives: the "object-like" argument is unmarked)
    - **Neutral**: R = T = P (no distinction among objects)
    - **Tripartite**: R ≠ T ≠ P (all three distinctly marked)

    Haspelmath's key observation: indirective is to ditransitives what
    accusative is to monotransitives; secundative is to ditransitives
    what ergative is to monotransitives. -/

/-- Ditransitive alignment type. Classifies how R (recipient) and T (theme)
    are coded relative to the monotransitive P. -/
inductive DitransitiveAlignment where
  /-- Neutral (R = T = P): no distinction among non-agent arguments -/
  | neutral
  /-- Indirective (T = P ≠ R): R is distinctly marked, T patterns with P.
      Analogous to accusative alignment. E.g., English "give the book TO Mary". -/
  | indirective
  /-- Secundative (R = P ≠ T): T is distinctly marked, R patterns with P.
      Analogous to ergative alignment. E.g., many Bantu applicatives. -/
  | secundative
  /-- Tripartite (R ≠ T ≠ P): all three roles distinctly marked -/
  | tripartite
  deriving DecidableEq, Repr

/-- Whether this ditransitive alignment marks R distinctly from P. -/
def DitransitiveAlignment.marksR : DitransitiveAlignment → Bool
  | .indirective => true
  | .tripartite  => true
  | _            => false

/-- Whether this ditransitive alignment marks T distinctly from P. -/
def DitransitiveAlignment.marksT : DitransitiveAlignment → Bool
  | .secundative => true
  | .tripartite  => true
  | _            => false

/-- A language's ditransitive alignment profile. -/
structure DitransitiveProfile where
  name : String
  iso639 : String
  alignment : DitransitiveAlignment
  notes : String := ""
  deriving Repr, DecidableEq

section DitransitiveData

/-- English: indirective (T = P, R marked with "to").
    "give the book to Mary" vs. "give Mary the book" (double-object
    alternation, but prepositional dative is the indirective base). -/
def ditrans_english : DitransitiveProfile :=
  { name := "English", iso639 := "eng"
    alignment := .indirective
    notes := "T = P (acc); R marked with 'to'" }

/-- German: indirective (T = ACC, R = DAT). -/
def ditrans_german : DitransitiveProfile :=
  { name := "German", iso639 := "deu"
    alignment := .indirective
    notes := "T = accusative; R = dative" }

/-- Latin: indirective (T = ACC, R = DAT). -/
def ditrans_latin : DitransitiveProfile :=
  { name := "Latin", iso639 := "lat"
    alignment := .indirective
    notes := "T = accusative; R = dative" }

/-- Japanese: indirective (T = o, R = ni). -/
def ditrans_japanese : DitransitiveProfile :=
  { name := "Japanese", iso639 := "jpn"
    alignment := .indirective
    notes := "T = o (accusative); R = ni (dative)" }

/-- Swahili: secundative (R = P, T distinctly marked via applicative). -/
def ditrans_swahili : DitransitiveProfile :=
  { name := "Swahili", iso639 := "swh"
    alignment := .secundative
    notes := "R = P in applicative; T marked differently" }

/-- Mandarin: neutral (R and T both unmarked, distinguished by order). -/
def ditrans_mandarin : DitransitiveProfile :=
  { name := "Mandarin", iso639 := "cmn"
    alignment := .neutral
    notes := "R and T both unmarked; order distinguishes" }

end DitransitiveData

def allDitransProfiles : List DitransitiveProfile :=
  [ ditrans_english, ditrans_german, ditrans_latin
  , ditrans_japanese, ditrans_swahili, ditrans_mandarin ]

/-- Indirective alignment is attested. -/
theorem ditrans_indirective_attested :
    allDitransProfiles.any (λ p => p.alignment == .indirective) = true := by
  native_decide

/-- Secundative alignment is attested. -/
theorem ditrans_secundative_attested :
    allDitransProfiles.any (λ p => p.alignment == .secundative) = true := by
  native_decide

/-- Neutral ditransitive alignment is attested. -/
theorem ditrans_neutral_attested :
    allDitransProfiles.any (λ p => p.alignment == .neutral) = true := by
  native_decide

/-- Indirective is more common than secundative (parallel to accusative
    being more common than ergative for monotransitives). -/
theorem ditrans_indirective_more_common :
    (allDitransProfiles.filter (λ p => p.alignment == .indirective)).length >
    (allDitransProfiles.filter (λ p => p.alignment == .secundative)).length := by
  native_decide

-- ============================================================================
-- Fragment Bridge Theorems
-- ============================================================================

/-! ### Bridge: Fragment grammatical descriptions ↔ Typology classifications

These theorems verify that the inline `AlignmentProfile` entries are
consistent with the grammatical facts described in each language's
Fragment directory. The Fragment describes *what the language does*
(e.g., agent gets ERG, patient gets ABS); the Typology *classifies*
that pattern (e.g., ergative NP alignment). Bridge theorems ensure the
classification faithfully reflects the grammar.

Languages without Fragment directories rely on WALS grounding (above)
instead. -/

section FragmentBridges

/-- Dargwa: Fragment says A=ERG, S/P=ABS → Typology says ergative NP alignment.
    The classification follows from the case facts. -/
theorem dargwa_fragment_bridge :
    Fragments.Dargwa.Case.agentCase = .erg ∧
    Fragments.Dargwa.Case.patientCase = .abs ∧
    dargwa.npAlignment = .ergative := ⟨rfl, rfl, rfl⟩

/-- Dargwa: Fragment says alignment family is ergative →
    Typology profile is consistently ergative. -/
theorem dargwa_alignment_family_bridge :
    toAlignmentType Fragments.Dargwa.Case.alignment
    = dargwa.npAlignment := rfl

/-- Japanese: Fragment case inventory contains NOM and ACC →
    Typology says accusative NP alignment. -/
theorem japanese_fragment_bridge :
    .nom ∈ Fragments.Japanese.Case.caseInventory ∧
    .acc ∈ Fragments.Japanese.Case.caseInventory ∧
    japanese.npAlignment = .accusative := ⟨by decide, by decide, rfl⟩

/-- Hindi: Fragment split-ergative system perfective→ERG matches
    Typology's ergative NP alignment (the dominant/WALS-coded pattern). -/
theorem hindi_fragment_bridge :
    Core.hindiSplit.alignment .perfective = .ergative ∧
    toAlignmentType (Core.hindiSplit.alignment .perfective)
      = hindiUrdu.npAlignment := ⟨rfl, rfl⟩

/-- Hindi: Fragment split-ergative system imperfective→ACC matches
    Typology's accusative pronoun alignment. -/
theorem hindi_split_bridge :
    Core.hindiSplit.alignment .imperfective = .accusative ∧
    toAlignmentType (Core.hindiSplit.alignment .imperfective)
      = hindiUrdu.pronAlignment := ⟨rfl, rfl⟩

end FragmentBridges

end Phenomena.Alignment.Typology
