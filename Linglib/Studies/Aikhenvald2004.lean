import Linglib.Typology.Modality
import Linglib.Fragments.English.Evidentiality
import Linglib.Fragments.French.Evidentiality
import Linglib.Fragments.German.Evidentiality
import Linglib.Fragments.Mandarin.Evidentiality
import Linglib.Fragments.Japanese.Evidentiality
import Linglib.Fragments.Korean.Evidentiality
import Linglib.Fragments.Turkish.Evidentiality
import Linglib.Fragments.Slavic.Bulgarian.Evidentiality
import Linglib.Fragments.Tibetan.Evidentiality
import Linglib.Fragments.Georgian.Evidentiality
import Linglib.Fragments.Quechua.Evidentiality
import Linglib.Fragments.Aymara.Evidentiality
import Linglib.Fragments.Tuyuca.Evidentiality
import Linglib.Fragments.Kashaya.Evidentiality
import Linglib.Fragments.Tariana.Evidentiality
import Linglib.Fragments.WestGreenlandic.Evidentiality
import Linglib.Fragments.Abkhaz.Evidentiality
import Linglib.Fragments.Finnish.Evidentiality

/-!
# Aikhenvald (2004): Evidentiality typology
@cite{aikhenvald-2004} @cite{de-haan-2013} @cite{barnes-1984} @cite{oswalt-1986}

Cross-linguistic typology of grammatical evidentiality, anchored on
Aikhenvald's *Evidentiality* (Oxford University Press, 2004) and contrasted
with @cite{de-haan-2013}'s WALS Ch 77/78 chapters.

This study file holds Aikhenvald's cross-linguistic generalisations on the
18-language sample. Per-language profiles live in
`Fragments/{Lang}/Evidentiality.lean` as `evidentialityProfile :
EvidentialityProfile` — constructed via `EvidentialityProfile.fromWALS` so
WALS Chs 77/78 are auto-pulled and the editorial fields (markers, notes,
attestedEvidentials, family) are local per-language commitments.

## Sample composition

18 languages chosen to span:
- **No-evidentials** (English, Mandarin — 2 languages per Aikhenvald;
  WALS additionally codes French, German, Japanese, Korean, Finnish as
  `indirectOnly` on a looser criterion).
- **Indirect-only** (Georgian, West Greenlandic — per Aikhenvald;
  WALS codes Georgian as directAndIndirect).
- **Direct + indirect** (Turkish, Bulgarian, Tibetan, Abkhaz —
  per Aikhenvald; WALS agrees on Turkish/Bulgarian, codes Abkhaz as
  indirectOnly).
- **Three-or-more** (Quechua, Aymara, Tuyuca, Kashaya, Tariana —
  per Aikhenvald; WALS has no entry for Quechua/Aymara, lumps
  Tuyuca/Kashaya/Tariana into directAndIndirect).

Aikhenvald's typology distinguishes 4-term and 5-term systems (Tuyuca and
Tariana have 5 obligatory categories: visual / nonvisual / inferred /
assumed / reported). The local `EvidentialSystem` enum collapses these into
`threeOrMore`; the `markers` field records the finer-grained inventory.

## Aikhenvald 2004 vs de Haan 2013 (WALS) divergences

10 of 18 sample languages diverge between Aikhenvald's analysis and de Haan's
WALS coding. The Studies file record-overrides per Aikhenvald and exposes
divergences as first-class theorems in §6 — making the cross-author
disagreement visible per linglib's interconnection-density thesis.

## What this file deliberately omits

Aggregate-count theorems (`sample_system_counts`, `sample_coding_counts`,
`sample_size`, etc.) trimmed per the no-aggregate-count anti-pattern memory
note. Substantive structural / implicational claims kept.
-/

set_option autoImplicit false

namespace Aikhenvald2004

open Typology.Modality

-- ============================================================================
-- §1. The 18-language exemplar sample (Aikhenvald 2004)
-- ============================================================================

/-! Per-language profiles drawn from `Fragments/{Lang}/Evidentiality.lean`
    via `EvidentialityProfile.fromWALS`. 10 languages are record-overridden
    where Aikhenvald 2004 disagrees with de Haan 2013 (WALS); see §6 for
    first-class divergence theorems. -/

-- Languages where Fragment WALS values match Aikhenvald: pass through directly.
private abbrev english := English.Evidentiality.evidentialityProfile
private abbrev mandarin := Mandarin.Evidentiality.evidentialityProfile
private abbrev turkish := Turkish.Evidentiality.evidentialityProfile
private abbrev bulgarian := Bulgarian.Evidentiality.evidentialityProfile
private abbrev tibetan := Tibetan.Evidentiality.evidentialityProfile
private abbrev quechua := Quechua.Evidentiality.evidentialityProfile
private abbrev aymara := Aymara.Evidentiality.evidentialityProfile
private abbrev westGreenlandic := WestGreenlandic.Evidentiality.evidentialityProfile

-- Aikhenvald-overrides: where Aikhenvald disagrees with WALS, record-update.
-- The WALS originals remain accessible at the Fragment paths.

/-- Aikhenvald 2004: French has no grammatical evidentials. WALS @cite{de-haan-2013}
    codes the journalistic-conditional reportative as `indirectOnly`. -/
private def french : EvidentialityProfile :=
  { French.Evidentiality.evidentialityProfile with
    system := .noGrammatical, coding := .notApplicable }

/-- Aikhenvald 2004: German has no grammatical evidentials. WALS counts modal
    verbs *sollen*/*wollen* as `indirectOnly`. -/
private def german : EvidentialityProfile :=
  { German.Evidentiality.evidentialityProfile with
    system := .noGrammatical, coding := .notApplicable }

/-- Aikhenvald 2004: Japanese has no grammatical evidentials. WALS counts
    *soo da* / *rashii* as `indirectOnly` with `verbalAffix` coding. -/
private def japanese : EvidentialityProfile :=
  { Japanese.Evidentiality.evidentialityProfile with
    system := .noGrammatical, coding := .notApplicable }

/-- Aikhenvald 2004: Korean has no grammatical evidentials. WALS counts
    *-deo-* retrospective as `indirectOnly`. -/
private def korean : EvidentialityProfile :=
  { Korean.Evidentiality.evidentialityProfile with
    system := .noGrammatical, coding := .notApplicable }

/-- Aikhenvald 2004: Finnish has no grammatical evidentials (modal verbs only).
    WALS counts these as `indirectOnly`. -/
private def finnish : EvidentialityProfile :=
  { Finnish.Evidentiality.evidentialityProfile with
    system := .noGrammatical, coding := .notApplicable }

/-- Aikhenvald 2004: Georgian has indirect-only evidentials (the evidential
    perfect marks inference/report only). WALS codes as `directAndIndirect`. -/
private def georgian : EvidentialityProfile :=
  { Georgian.Evidentiality.evidentialityProfile with
    system := .indirectOnly }

/-- Aikhenvald 2004: Abkhaz has 2-way direct/indirect via TAM-fused finite vs
    nonfinite-plus-copula. WALS codes as `indirectOnly`/`verbalAffix`. -/
private def abkhaz : EvidentialityProfile :=
  { Abkhaz.Evidentiality.evidentialityProfile with
    system := .directAndIndirect, coding := .partOfTAM }

/-- Aikhenvald 2004: Tuyuca has 5-term system (visual/nonvisual/apparent/
    secondhand/assumed) per @cite{barnes-1984}. WALS lumps into `directAndIndirect`
    with `partOfTAM` coding. -/
private def tuyuca : EvidentialityProfile :=
  { Tuyuca.Evidentiality.evidentialityProfile with
    system := .threeOrMore, coding := .verbalAffix }

/-- Aikhenvald 2004: Kashaya has 5-term system distinguishing visual from
    auditory direct evidence per @cite{oswalt-1986}. WALS lumps into
    `directAndIndirect`. -/
private def kashaya : EvidentialityProfile :=
  { Kashaya.Evidentiality.evidentialityProfile with
    system := .threeOrMore }

/-- Aikhenvald 2004: Tariana has 5-term system (Vaupés multilingual area).
    WALS lumps into `directAndIndirect` with `partOfTAM` coding. -/
private def tariana : EvidentialityProfile :=
  { Tariana.Evidentiality.evidentialityProfile with
    system := .threeOrMore, coding := .verbalAffix }

/-- 18-language Aikhenvald sample. -/
def allLanguages : List EvidentialityProfile :=
  [ english, french, german, mandarin, japanese, korean
  , turkish, bulgarian, tibetan
  , georgian, westGreenlandic
  , quechua, aymara, tuyuca, kashaya, tariana
  , abkhaz, finnish ]

-- ============================================================================
-- §2. Cross-chapter consistency (Aikhenvald)
-- ============================================================================

set_option maxRecDepth 2000 in
/-- Every language without grammatical evidentials has `notApplicable` coding. -/
theorem no_evidentials_implies_na_coding :
    ∀ p ∈ allLanguages, p.system = .noGrammatical → p.coding = .notApplicable := by
  decide

set_option maxRecDepth 2000 in
/-- Every language with grammatical evidentials has a non-trivial coding. -/
theorem evidentials_implies_real_coding :
    ∀ p ∈ allLanguages, p.HasEvidentials → p.coding ≠ .notApplicable := by decide

set_option maxRecDepth 2000 in
/-- The system and coding fields are consistent: noGrammatical iff notApplicable. -/
theorem system_coding_consistency :
    ∀ p ∈ allLanguages,
      (p.system = .noGrammatical ↔ p.coding = .notApplicable) := by decide

-- ============================================================================
-- §3. Implicational hierarchy
-- ============================================================================

set_option maxRecDepth 2000 in
/-- Languages with three-or-more evidential choices always include a direct
    evidence category. Follows from the type definition; verified against
    the sample. -/
theorem three_or_more_always_has_direct :
    ∀ p ∈ allLanguages, p.system = .threeOrMore → p.HasDirect := by decide

set_option maxRecDepth 2000 in
/-- Every language with direct evidence has either two-choice or three-or-more
    (never indirect-only or no-evidentials). -/
theorem direct_implies_at_least_two_choices :
    ∀ p ∈ allLanguages, p.HasDirect →
      p.system = .directAndIndirect ∨ p.system = .threeOrMore := by decide

/-- The complexity hierarchy: noGrammatical < indirectOnly < directAndIndirect
    < threeOrMore. -/
theorem evidential_complexity_hierarchy :
    EvidentialSystem.numChoices .threeOrMore >
    EvidentialSystem.numChoices .directAndIndirect ∧
    EvidentialSystem.numChoices .directAndIndirect >
    EvidentialSystem.numChoices .indirectOnly ∧
    EvidentialSystem.numChoices .indirectOnly >
    EvidentialSystem.numChoices .noGrammatical := by decide

-- ============================================================================
-- §4. Areal generalisations
-- ============================================================================

/-- Western European languages (English, French, German per Aikhenvald) all
    lack grammatical evidentials. The Balkan Sprachbund is the notable
    exception (covered by Bulgarian). -/
theorem western_european_no_evidentials :
    english.system = .noGrammatical ∧
    french.system = .noGrammatical ∧
    german.system = .noGrammatical := by decide

/-- East Asian languages (Mandarin, Japanese, Korean per Aikhenvald) all lack
    grammatical evidentials. East Asia is an evidential-free zone. -/
theorem east_asian_no_evidentials :
    mandarin.system = .noGrammatical ∧
    japanese.system = .noGrammatical ∧
    korean.system = .noGrammatical := by decide

/-- Andean evidential cluster: Quechua and Aymara both have three-or-more
    systems coded as verbal affixes. Well-known areal feature. -/
theorem andean_evidential_cluster :
    quechua.system = .threeOrMore ∧ aymara.system = .threeOrMore ∧
    quechua.coding = .verbalAffix ∧ aymara.coding = .verbalAffix := by decide

/-- Vaupés-Amazonian rich evidential systems: Tuyuca and Tariana, from
    different families but in contact in the Vaupés, both have
    three-or-more categories with five distinctions each. -/
theorem amazonian_rich_systems :
    tuyuca.system = .threeOrMore ∧ tariana.system = .threeOrMore ∧
    tuyuca.coding = .verbalAffix ∧ tariana.coding = .verbalAffix := by decide

/-- Americas languages (Quechua, Aymara, Tuyuca, Kashaya, Tariana) all have
    three-or-more systems via verbal affixes. The Americas have the highest
    density of complex evidential systems. -/
theorem americas_all_complex_evidentials :
    ∀ p ∈ [quechua, aymara, tuyuca, kashaya, tariana],
      p.system = .threeOrMore ∧ p.coding = .verbalAffix := by decide

/-- TAM-fused evidentiality is characteristic of the Balkans and Caucasus.
    In the sample: Turkish, Bulgarian, Georgian, Abkhaz. -/
theorem tam_fusion_in_sample :
    turkish.coding = .partOfTAM ∧ bulgarian.coding = .partOfTAM ∧
    georgian.coding = .partOfTAM ∧ abkhaz.coding = .partOfTAM := by decide

-- ============================================================================
-- §5. Coding-strategy generalisations
-- ============================================================================

set_option maxRecDepth 2000 in
/-- All languages with three-or-more systems use verbal affixes. -/
theorem complex_systems_use_affixes :
    ∀ p ∈ allLanguages, p.system = .threeOrMore → p.coding = .verbalAffix := by
  decide

-- ============================================================================
-- §6. Aikhenvald 2004 vs de Haan 2013 (WALS) divergence theorems
-- ============================================================================

/-! 10 of 18 sample languages diverge between Aikhenvald's analysis and
    de Haan's WALS coding. The Aikhenvald values are this Studies file's
    record-overrides; the WALS values are the Fragment-side
    `Fragments.{Lang}.Evidentiality.evidentialityProfile` (which goes
    through `EvidentialityProfile.fromWALS`). Linglib's
    interconnection-density thesis: incompatibilities visible. -/

/-- Aikhenvald vs de Haan: French. Aikhenvald says no grammatical evidentials;
    de Haan's WALS Ch 77 codes the journalistic-conditional reportative as
    `indirectOnly`. -/
theorem french_aikhenvald_vs_de_haan :
    french.system = .noGrammatical ∧
    French.Evidentiality.evidentialityProfile.system = .indirectOnly := by
  decide

/-- Aikhenvald vs de Haan: German. Aikhenvald excludes modal *sollen*/*wollen*
    from grammatical evidentials; WALS counts them. -/
theorem german_aikhenvald_vs_de_haan :
    german.system = .noGrammatical ∧
    German.Evidentiality.evidentialityProfile.system = .indirectOnly := by
  decide

/-- Aikhenvald vs de Haan: Japanese. Aikhenvald treats *soo da*/*rashii* as
    modal, not evidential; WALS classifies them as `indirectOnly`. -/
theorem japanese_aikhenvald_vs_de_haan :
    japanese.system = .noGrammatical ∧
    Japanese.Evidentiality.evidentialityProfile.system = .indirectOnly := by
  decide

/-- Aikhenvald vs de Haan: Korean. Aikhenvald excludes *-deo-* from
    grammatical evidentials. -/
theorem korean_aikhenvald_vs_de_haan :
    korean.system = .noGrammatical ∧
    Korean.Evidentiality.evidentialityProfile.system = .indirectOnly := by
  decide

/-- Aikhenvald vs de Haan: Finnish. Aikhenvald excludes modal verbs from
    grammatical evidentials. -/
theorem finnish_aikhenvald_vs_de_haan :
    finnish.system = .noGrammatical ∧
    Finnish.Evidentiality.evidentialityProfile.system = .indirectOnly := by
  decide

/-- Aikhenvald vs de Haan: Georgian. Aikhenvald says indirect-only;
    WALS Ch 77 codes as direct-and-indirect. -/
theorem georgian_aikhenvald_vs_de_haan :
    georgian.system = .indirectOnly ∧
    Georgian.Evidentiality.evidentialityProfile.system =
      .directAndIndirect := by decide

/-- Aikhenvald vs de Haan: Abkhaz. Aikhenvald says direct-and-indirect with
    TAM-fusion; WALS codes as indirect-only with verbal-affix coding. -/
theorem abkhaz_aikhenvald_vs_de_haan :
    abkhaz.system = .directAndIndirect ∧ abkhaz.coding = .partOfTAM ∧
    Abkhaz.Evidentiality.evidentialityProfile.system = .indirectOnly ∧
    Abkhaz.Evidentiality.evidentialityProfile.coding = .verbalAffix := by
  decide

/-- Aikhenvald vs de Haan: Tuyuca. Aikhenvald distinguishes 5-term system
    (visual/nonvisual/apparent/secondhand/assumed); WALS Ch 77 lumps into
    the `directAndIndirect` 2-way bucket and Ch 78 codes as `partOfTAM`. -/
theorem tuyuca_aikhenvald_vs_de_haan :
    tuyuca.system = .threeOrMore ∧ tuyuca.coding = .verbalAffix ∧
    Tuyuca.Evidentiality.evidentialityProfile.system = .directAndIndirect ∧
    Tuyuca.Evidentiality.evidentialityProfile.coding = .partOfTAM := by
  decide

/-- Aikhenvald vs de Haan: Kashaya. Aikhenvald distinguishes 4-or-5-way
    system; WALS lumps into `directAndIndirect`. -/
theorem kashaya_aikhenvald_vs_de_haan :
    kashaya.system = .threeOrMore ∧
    Kashaya.Evidentiality.evidentialityProfile.system =
      .directAndIndirect := by decide

/-- Aikhenvald vs de Haan: Tariana. Aikhenvald distinguishes 5-term system
    (Vaupés area); WALS lumps into `directAndIndirect` and codes as `partOfTAM`. -/
theorem tariana_aikhenvald_vs_de_haan :
    tariana.system = .threeOrMore ∧ tariana.coding = .verbalAffix ∧
    Tariana.Evidentiality.evidentialityProfile.system = .directAndIndirect ∧
    Tariana.Evidentiality.evidentialityProfile.coding = .partOfTAM := by
  decide

end Aikhenvald2004
