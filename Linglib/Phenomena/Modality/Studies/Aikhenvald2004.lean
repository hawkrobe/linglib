import Linglib.Typology.Modality

/-!
# Aikhenvald (2004) + de Haan (2013): Evidentiality typology
@cite{aikhenvald-2004} @cite{de-haan-2013} @cite{barnes-1984}
@cite{oswalt-1986}

Cross-linguistic typology of grammatical evidentiality, anchored on
Aikhenvald's *Evidentiality* (Oxford University Press, 2004) and
@cite{de-haan-2013}'s WALS Ch 77/78 chapters.

This study file holds the 18-language exemplar sample and cross-linguistic
generalisations consuming the substrate `EvidentialityProfile`. WALS
aggregate distribution theorems live in `Linglib/Typology/Modality.lean`.
Per-language Fragment-vs-WALS data-equality theorems are deliberately
absent — see `feedback_no_per_lang_wals_grounding_in_studies` for the
rationale.

## Sample composition

18 languages chosen to span:
- **No-evidentials** (English, French, German, Mandarin, Japanese, Korean,
  Finnish — 7 languages): the "evidential-free zone" of Western Europe and
  East Asia.
- **Indirect-only** (Georgian, West Greenlandic — 2 languages).
- **Direct + indirect** (Turkish, Bulgarian, Tibetan, Abkhaz — 4 languages):
  the Balkan + Caucasus + Tibetan area.
- **Three-or-more** (Quechua, Aymara, Tuyuca, Kashaya, Tariana — 5 languages):
  the Andean + Amazonian areas with the richest evidential systems.

@cite{aikhenvald-2004} 's typology distinguishes 4-term and 5-term systems
(Tuyuca and Tariana have 5 obligatory categories: visual / nonvisual /
inferred / assumed / reported). Our `EvidentialSystem` enum collapses these
into `threeOrMore`; the `markers` field records the finer-grained inventory.
-/

set_option autoImplicit false

namespace Phenomena.Modality.Studies.Aikhenvald2004

open Typology.Modality

-- ============================================================================
-- §1. The 18-language exemplar sample
-- ============================================================================

/-- English. No grammatical evidentials; evidential source is conveyed
    lexically by adverbs ("apparently", "reportedly") or hedging
    expressions, never by obligatory verbal morphology. -/
def english : EvidentialityProfile :=
  { language := "English", iso := "eng", family := "Indo-European"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "Lexical evidentials only: apparently, reportedly, evidently" }

/-- French. No grammatical evidentials. The conditional has secondary
    reportative use in journalistic French ("le president serait malade")
    but is not a dedicated evidential. -/
def french : EvidentialityProfile :=
  { language := "French", iso := "fra", family := "Indo-European"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "Conditional has secondary reportative use in journalistic register" }

/-- German. No grammatical evidentials. Modal verbs *sollen* (reportative)
    and *wollen* (self-report) have evidential-like uses but are full modal
    verbs. -/
def german : EvidentialityProfile :=
  { language := "German", iso := "deu", family := "Indo-European"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "sollen/wollen have evidential uses but are modal verbs" }

/-- Mandarin Chinese. No grammatical evidentials. Lexical strategies:
    *tinshuo* (听说, 'I hear that'), *juede* (觉得, 'I feel that'),
    sentence-final *ba* (吧). -/
def mandarin : EvidentialityProfile :=
  { language := "Mandarin", iso := "cmn", family := "Sino-Tibetan"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "Lexical evidential strategies: tinshuo, juede; no obligatory marking" }

/-- Japanese. No grammatical evidentials in the strict sense. Hearsay
    *soo da* and inferential *rashii* are analyzed as modal rather than
    evidential by @cite{de-haan-2013}. -/
def japanese : EvidentialityProfile :=
  { language := "Japanese", iso := "jpn", family := "Japonic"
  , system := .noGrammatical, coding := .notApplicable
  , markers := ["soo da", "rashii"]
  , notes := "soo da (hearsay) and rashii (inferential) are modal, not " ++
             "grammaticalized evidentials per de Haan (2013)" }

/-- Korean. No grammatical evidentials per WALS. *-deo-* (retrospective)
    has evidential-like function but is not classified as grammaticalized
    evidential. -/
def korean : EvidentialityProfile :=
  { language := "Korean", iso := "kor", family := "Koreanic"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "-deo- (retrospective) has evidential-like function but is " ++
             "not classified as grammatical evidential in WALS" }

/-- Turkish. Two-choice direct vs indirect. Past-tense paradigm contrasts
    *-DI* (witnessed) with *-mIş* (inferred or reported). The canonical
    indirect-evidential of a major language. Fused with TAM. -/
def turkish : EvidentialityProfile :=
  { language := "Turkish", iso := "tur", family := "Turkic"
  , system := .directAndIndirect, coding := .partOfTAM
  , markers := ["-DI (direct)", "-mIş (indirect)"]
  , notes := "Evidential distinction fused with past tense; -DI = witnessed, " ++
             "-mIş = inferred/reported" }

/-- Bulgarian. Two-choice direct vs indirect. The best-known European
    language with grammatical evidentials. Aorist (direct) vs l-form
    (indirect), fused with TAM. Balkan Sprachbund. -/
def bulgarian : EvidentialityProfile :=
  { language := "Bulgarian", iso := "bul", family := "Indo-European"
  , system := .directAndIndirect, coding := .partOfTAM
  , markers := ["aorist (direct)", "l-form (indirect)"]
  , notes := "Balkan evidentiality; direct (aorist) vs indirect (l-participle " ++
             "based forms); fused with tense-aspect" }

/-- Tibetan (Lhasa). Two-choice direct vs indirect via copula/auxiliary
    contrast. *red*/*yod* (personal knowledge) vs *yin*/*'dug* (indirect
    or new information). Egophoric system. -/
def tibetan : EvidentialityProfile :=
  { language := "Tibetan (Lhasa)", iso := "bod", family := "Sino-Tibetan"
  , system := .directAndIndirect, coding := .particle
  , markers := ["red (direct)", "'dug (indirect)", "yod (direct)", "yin (indirect)"]
  , notes := "Egophoric system; direct/personal knowledge vs indirect/new info; " ++
             "expressed via copula and auxiliary contrasts" }

/-- Georgian. Indirect evidential only. Evidential perfect ("I screeve")
    marks inference or report; no dedicated direct-evidence marker. Fused
    with TAM. -/
def georgian : EvidentialityProfile :=
  { language := "Georgian", iso := "kat", family := "Kartvelian"
  , system := .indirectOnly, coding := .partOfTAM
  , markers := ["evidential perfect (I screeve)"]
  , notes := "Evidential perfect for inference/report; no dedicated direct marker; " ++
             "fused with tense-aspect screeve system" }

/-- Cuzco Quechua. Three-or-more system: direct *-mi*, reportative *-si*,
    conjectural *-chá*. Obligatory enclitics on finite clauses. Canonical
    Andean evidential system. -/
def quechua : EvidentialityProfile :=
  { language := "Quechua (Cuzco)", iso := "quz", family := "Quechuan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-mi (direct)", "-si (reportative)", "-chá (conjectural)"]
  , notes := "Canonical three-way system: direct/reportative/conjectural; " ++
             "obligatory on finite clauses" }

/-- Aymara. Three-or-more system: direct, reportative, non-personal/
    inferential. Andean areal feature shared with Quechua. -/
def aymara : EvidentialityProfile :=
  { language := "Aymara", iso := "aym", family := "Aymaran"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-wa (direct)", "-sa (reportative)", "-pacha (inferential)"]
  , notes := "Obligatory three-way system; Andean areal feature shared " ++
             "with Quechua" }

/-- Tuyuca. Five-term system: visual, nonvisual, apparent (inferential),
    secondhand (reported), assumed. Obligatory verbal suffixes.
    @cite{barnes-1984} is the classic description. Vaupés multilingual area. -/
def tuyuca : EvidentialityProfile :=
  { language := "Tuyuca", iso := "tue", family := "Tucanoan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-wi (visual)", "-ti (nonvisual)", "-yi (apparent)",
                "-yigi (secondhand)", "-hiyi (assumed)"]
  , notes := "Five-way evidential system: visual/nonvisual/apparent/" ++
             "secondhand/assumed; obligatory verbal suffixes; " ++
             "Barnes (1984)" }

/-- Kashaya. Five-term system distinguishing visual from auditory direct
    evidence. @cite{oswalt-1986}. -/
def kashaya : EvidentialityProfile :=
  { language := "Kashaya", iso := "kju", family := "Pomoan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-ya (performative)", "-ʔ (visual)", "-inne (auditory)",
                "-qa (inferential)", "-do (reportative)"]
  , notes := "Four-way sensory+inferential+reportative; distinguishes " ++
             "visual from auditory direct evidence; Oswalt (1986)" }

/-- Tariana. Five-term system in the Vaupés multilingual area: visual,
    nonvisual, inferred, assumed, reported. -/
def tariana : EvidentialityProfile :=
  { language := "Tariana", iso := "tae", family := "Arawakan"
  , system := .threeOrMore, coding := .verbalAffix
  , markers := ["-ka (visual)", "-mha (nonvisual)", "-nihka (inferred)",
                "-sika (assumed)", "-pidaka (reported)"]
  , notes := "Five-way system; Vaupés multilingual area; " ++
             "Aikhenvald (2003, 2004)" }

/-- West Greenlandic. Indirect only — inferential mood via verbal suffix;
    no dedicated direct-evidence marker. -/
def westGreenlandic : EvidentialityProfile :=
  { language := "West Greenlandic", iso := "kal", family := "Eskimo-Aleut"
  , system := .indirectOnly, coding := .verbalAffix
  , markers := ["-gunarpoq (inferential mood)"]
  , notes := "Inferential mood only; no dedicated direct marker" }

/-- Abkhaz. Two-choice direct vs indirect, fused with TAM. -/
def abkhaz : EvidentialityProfile :=
  { language := "Abkhaz", iso := "abk", family := "Northwest Caucasian"
  , system := .directAndIndirect, coding := .partOfTAM
  , markers := ["finite verb (direct)", "nonfinite + copula (indirect)"]
  , notes := "Evidential fused with tense-aspect; Caucasus areal feature" }

/-- Finnish. No grammatical evidentials; modality via modal verbs. -/
def finnish : EvidentialityProfile :=
  { language := "Finnish", iso := "fin", family := "Uralic"
  , system := .noGrammatical, coding := .notApplicable
  , notes := "No grammatical evidentials; modality via modal verbs " ++
             "(voida 'can', täytyä 'must', saattaa 'may')" }

/-- All language profiles in the sample. -/
def allLanguages : List EvidentialityProfile :=
  [ english, french, german, mandarin, japanese, korean
  , turkish, bulgarian, tibetan
  , georgian, westGreenlandic
  , quechua, aymara, tuyuca, kashaya, tariana
  , abkhaz, finnish ]

-- ============================================================================
-- §2. Sample-level distributions
-- ============================================================================

theorem sample_size : allLanguages.length = 18 := by native_decide

/-- System type distribution in the sample. -/
theorem sample_system_counts :
    countBySystem allLanguages .noGrammatical = 7 ∧
    countBySystem allLanguages .indirectOnly = 2 ∧
    countBySystem allLanguages .directAndIndirect = 4 ∧
    countBySystem allLanguages .threeOrMore = 5 := by
  native_decide

/-- Coding strategy distribution in the sample. -/
theorem sample_coding_counts :
    countByCoding allLanguages .verbalAffix = 6 ∧
    countByCoding allLanguages .clitic = 0 ∧
    countByCoding allLanguages .particle = 1 ∧
    countByCoding allLanguages .partOfTAM = 4 ∧
    countByCoding allLanguages .notApplicable = 7 := by
  native_decide

/-- Languages with evidentials in the sample. -/
theorem sample_has_evidentials_count :
    (allLanguages.filter (·.hasEvidentials)).length = 11 := by native_decide

/-- Languages with direct evidence marking in the sample. -/
theorem sample_has_direct_count :
    (allLanguages.filter (·.hasDirect)).length = 9 := by native_decide

-- ============================================================================
-- §3. Cross-chapter consistency
-- ============================================================================

/-- Every language without grammatical evidentials has a `notApplicable`
    coding. -/
theorem no_evidentials_implies_na_coding :
    let noEvid := allLanguages.filter (·.system == .noGrammatical)
    noEvid.all (·.coding == .notApplicable) = true := by native_decide

/-- Every language with grammatical evidentials has a real coding. -/
theorem evidentials_implies_real_coding :
    let withEvid := allLanguages.filter (·.hasEvidentials)
    withEvid.all (·.coding != .notApplicable) = true := by native_decide

/-- The system and coding fields are consistent: the set of languages with
    `notApplicable` coding equals the set with `noGrammatical` system. -/
theorem system_coding_consistency :
    allLanguages.all (λ p =>
      (p.system == .noGrammatical) == (p.coding == .notApplicable)) = true := by
  native_decide

-- ============================================================================
-- §4. Implicational hierarchy
-- ============================================================================

/-- Languages with three or more evidential choices always include a direct
    evidence category. Follows from the type definition; verified against
    the sample. -/
theorem three_or_more_always_has_direct :
    let threeOrMore := allLanguages.filter (·.system == .threeOrMore)
    threeOrMore.all (·.hasDirect) = true := by native_decide

/-- Every language with direct evidence has either a two-choice or
    three-or-more system (never indirect-only or no-evidentials). -/
theorem direct_implies_at_least_two_choices :
    let withDirect := allLanguages.filter (·.hasDirect)
    withDirect.all (λ p => p.system == .directAndIndirect ||
                           p.system == .threeOrMore) = true := by
  native_decide

/-- The complexity hierarchy: noGrammatical < indirectOnly < directAndIndirect
    < threeOrMore. -/
theorem evidential_complexity_hierarchy :
    EvidentialSystem.numChoices .threeOrMore >
    EvidentialSystem.numChoices .directAndIndirect ∧
    EvidentialSystem.numChoices .directAndIndirect >
    EvidentialSystem.numChoices .indirectOnly ∧
    EvidentialSystem.numChoices .indirectOnly >
    EvidentialSystem.numChoices .noGrammatical := by
  native_decide

-- ============================================================================
-- §5. Areal generalisations
-- ============================================================================

/-- Western European languages in the sample (English, French, German) all
    lack grammatical evidentials. The Balkan Sprachbund is the notable
    exception (covered by Bulgarian). -/
def westernEuropean : List EvidentialityProfile := [english, french, german]

theorem western_european_no_evidentials :
    westernEuropean.all (·.system == .noGrammatical) = true := by native_decide

/-- East Asian languages in the sample (Mandarin, Japanese, Korean) all lack
    grammatical evidentials. East Asia is an evidential-free zone. -/
def eastAsian : List EvidentialityProfile := [mandarin, japanese, korean]

theorem east_asian_no_evidentials :
    eastAsian.all (·.system == .noGrammatical) = true := by native_decide

/-- Andean evidential cluster: Quechua and Aymara both have three-or-more
    systems coded as verbal affixes. Well-known areal feature. -/
theorem andean_evidential_cluster :
    quechua.system = .threeOrMore ∧ aymara.system = .threeOrMore ∧
    quechua.coding = .verbalAffix ∧ aymara.coding = .verbalAffix := by
  native_decide

/-- Vaupés-Amazonian rich evidential systems: Tuyuca and Tariana, from
    different families but in contact in the Vaupés, both have
    three-or-more categories with five distinctions each. -/
theorem amazonian_rich_systems :
    tuyuca.system = .threeOrMore ∧ tariana.system = .threeOrMore ∧
    tuyuca.coding = .verbalAffix ∧ tariana.coding = .verbalAffix := by
  native_decide

/-- Americas languages in the sample (Quechua, Aymara, Tuyuca, Kashaya,
    Tariana) all have three-or-more systems via verbal affixes. The
    Americas have the highest density of complex evidential systems. -/
def americas : List EvidentialityProfile :=
  [quechua, aymara, tuyuca, kashaya, tariana]

theorem americas_all_complex_evidentials :
    americas.all (·.system == .threeOrMore) = true := by native_decide

theorem americas_all_verbal_affix :
    americas.all (·.coding == .verbalAffix) = true := by native_decide

/-- TAM-fused evidentiality is characteristic of the Balkans and Caucasus.
    In the sample: Turkish, Bulgarian, Georgian, Abkhaz. -/
theorem tam_fusion_in_sample :
    turkish.coding = .partOfTAM ∧
    bulgarian.coding = .partOfTAM ∧
    georgian.coding = .partOfTAM ∧
    abkhaz.coding = .partOfTAM := by
  native_decide

-- ============================================================================
-- §6. Coding-strategy generalisations
-- ============================================================================

/-- All languages with three-or-more systems in the sample use verbal
    affixes. Consistent with the cross-linguistic pattern that complex
    evidential systems use morphologically integrated coding. -/
theorem complex_systems_use_affixes :
    let complex := allLanguages.filter (·.system == .threeOrMore)
    complex.all (·.coding == .verbalAffix) = true := by native_decide

end Phenomena.Modality.Studies.Aikhenvald2004
