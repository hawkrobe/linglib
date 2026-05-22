import Linglib.Typology.Gender
import Linglib.Core.Agreement.Target
import Linglib.Fragments.English.Gender
import Linglib.Fragments.Mandarin.Gender
import Linglib.Fragments.Japanese.Gender
import Linglib.Fragments.Turkish.Gender
import Linglib.Fragments.Finnish.Gender
import Linglib.Fragments.Korean.Gender
import Linglib.Fragments.Quechua.Gender
import Linglib.Fragments.French.Gender
import Linglib.Fragments.Spanish.Gender
import Linglib.Fragments.Hindi.Gender
import Linglib.Fragments.Irish.Gender
import Linglib.Fragments.Hebrew.Gender
import Linglib.Fragments.Hausa.Gender
import Linglib.Fragments.German.Gender
import Linglib.Fragments.Slavic.Russian.Gender
import Linglib.Fragments.Latin.Gender
import Linglib.Fragments.Romanian.Gender
import Linglib.Fragments.Dyirbal.Gender
import Linglib.Fragments.Georgian.Gender
import Linglib.Fragments.Swahili.Gender
import Linglib.Fragments.Zulu.Gender
import Linglib.Fragments.Fula.Gender

/-!
# Corbett (1991): Gender — typology of noun-class systems
@cite{corbett-1991} @cite{corbett-2013} @cite{dryer-haspelmath-2013}
@cite{dixon-1972}

Greville Corbett. *Gender*. Cambridge University Press, 1991.
Plus @cite{corbett-2013}'s WALS Chs 30, 31, 32.

This study file holds Corbett's cross-linguistic generalisations on the
22-language sample. Per-language profiles live in
`Fragments/{Lang}/Gender.lean` as `genderTypology : GenderProfile` —
constructed via `GenderProfile.fromWALS` so WALS Chs 30/31/32 are
auto-pulled and the editorial fields (rawGenderCount, agreementTargets,
semanticBases, attestedSurfaceGenders) are local per-language commitments.

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

## What this file deliberately omits

Aggregate-count theorems (`sample_X_count = N`, `gender_scale_range`,
`sample_diversity`) — these go stale every time a Fragment is added to
the sample and were the "aggregate-count theorems" anti-pattern. The
substantive Corbett 1991 generalisations (Agreement Hierarchy properties,
no-purely-formal claim, basis × count interactions) are kept; ISO sanity
remains as a drift sentry.
-/

set_option autoImplicit false

namespace Corbett1991

open Typology.Gender
open Core (AgreementTarget)

-- ============================================================================
-- §1. The 22-language exemplar sample
-- ============================================================================

/-! Per-language profiles drawn from `Fragments/{Lang}/Gender.lean` via
    `GenderProfile.fromWALS`. Aliases here for concise reference below.

    Three languages are record-updated to match Corbett's 1991 monograph
    where it diverges from his later WALS chapters @cite{corbett-2013}.
    The divergences are first-class theorems in §9 below — exposing them
    rather than hiding them inside the Fragment. -/

private abbrev mandarin  := Fragments.Mandarin.Gender.genderTypology
private abbrev japanese  := Fragments.Japanese.Gender.genderTypology
private abbrev turkish   := Fragments.Turkish.Gender.genderTypology
private abbrev finnish   := Fragments.Finnish.Gender.genderTypology
private abbrev korean    := Fragments.Korean.Gender.genderTypology
private abbrev quechua   := Fragments.Quechua.Gender.genderTypology
private abbrev french    := Fragments.French.Gender.genderTypology
private abbrev spanish   := Fragments.Spanish.Gender.genderTypology
private abbrev hindiUrdu := Fragments.Hindi.Gender.genderTypology
private abbrev irish     := Fragments.Irish.Gender.genderTypology
private abbrev hebrew    := Fragments.Hebrew.Gender.genderTypology
private abbrev hausa     := Fragments.Hausa.Gender.genderTypology
private abbrev german    := Fragments.German.Gender.genderTypology
private abbrev russian   := Fragments.Slavic.Russian.Gender.genderTypology
private abbrev latin     := Fragments.Latin.Gender.genderTypology
private abbrev romanian  := Fragments.Romanian.Gender.genderTypology
private abbrev swahili   := Fragments.Swahili.Gender.genderTypology
private abbrev zulu      := Fragments.Zulu.Gender.genderTypology
private abbrev fula      := Fragments.Fula.Gender.genderTypology

/-! Corbett-1991 record-overrides for the 3 languages where Corbett's 1991
    book disagrees with his 2013 WALS chapters. -/

/-- Corbett 1991: English has no grammatical gender (the *he/she/it*
    pronoun distinction is natural gender, not a controller-marked system).
    WALS @cite{corbett-2013} F30A says 3-gender. Override here. -/
private def english : GenderProfile :=
  { Fragments.English.Gender.genderTypology with
    genderCount := .none, rawGenderCount := 0
    basis := .noGender, assignment := .noGender
    agreementTargets := [], semanticBases := []
    attestedSurfaceGenders := [] }

/-- Corbett 1991: Dyirbal is 4-class non-sex-based (the system's organising
    criteria cut across biological sex). WALS @cite{corbett-2013} F31A says
    sex-based on the narrow "Class I includes males" criterion. Override. -/
private def dyirbal : GenderProfile :=
  { Fragments.Dyirbal.Gender.genderTypology with
    basis := .nonSexBased }

/-- Corbett 1991: Georgian is a 4-class non-sex-based gender system on the
    rationality/animacy split (agreement on pronouns + verbs). WALS
    @cite{corbett-2013} F30A/31A/32A says no gender on the noun-side-marking
    criterion. Override. -/
private def georgian : GenderProfile :=
  { Fragments.Georgian.Gender.genderTypology with
    genderCount := .four, rawGenderCount := 4
    basis := .nonSexBased, assignment := .semanticOnly
    agreementTargets := [.personalPronoun, .verb]
    semanticBases := [.rationality, .animacy] }

/-- All 22 language profiles in the Corbett 1991 sample. English, Dyirbal,
    and Georgian are the record-overridden versions; the WALS originals
    are at `Fragments.{English,Dyirbal,Georgian}.Gender.genderTypology`. -/
def allProfiles : List GenderProfile :=
  [ english, mandarin, japanese, turkish, finnish, korean, quechua
  , french, spanish, hindiUrdu, irish, hebrew, hausa
  , german, russian, latin, romanian
  , dyirbal, georgian
  , swahili, zulu, fula ]

-- ============================================================================
-- §2. Sample-level structural sanity
-- ============================================================================

/-- All raw gender counts are consistent with their WALS bins. -/
theorem all_raw_consistent :
    ∀ p ∈ allProfiles, p.IsRawCountConsistent := by decide

/-- All profiles are cross-chapter consistent. -/
theorem all_cross_consistent :
    ∀ p ∈ allProfiles, p.IsCrossChapterConsistent := by decide

/-- All five `GenderCount` values are attested. -/
theorem all_gender_counts_attested :
    (∃ p ∈ allProfiles, p.genderCount = .none) ∧
    (∃ p ∈ allProfiles, p.genderCount = .two) ∧
    (∃ p ∈ allProfiles, p.genderCount = .three) ∧
    (∃ p ∈ allProfiles, p.genderCount = .four) ∧
    (∃ p ∈ allProfiles, p.genderCount = .fivePlus) := by decide

/-- All three `GenderBasis` values are attested. -/
theorem all_bases_attested :
    (∃ p ∈ allProfiles, p.basis = .noGender) ∧
    (∃ p ∈ allProfiles, p.basis = .sexBased) ∧
    (∃ p ∈ allProfiles, p.basis = .nonSexBased) := by decide

/-- All three `AssignmentSystem` values are attested. -/
theorem all_assignments_attested :
    (∃ p ∈ allProfiles, p.assignment = .noGender) ∧
    (∃ p ∈ allProfiles, p.assignment = .semanticOnly) ∧
    (∃ p ∈ allProfiles, p.assignment = .semanticAndFormal) := by decide

-- ============================================================================
-- §3. Cross-linguistic generalisations (Corbett 1991)
-- ============================================================================

/-- All 2- and 3-gender systems in the sample are sex-based. Reflects the
    cross-linguistic pattern that small gender systems organise around sex. -/
theorem two_three_gender_all_sex_based :
    ∀ p ∈ allProfiles,
      p.genderCount = .two ∨ p.genderCount = .three →
        p.basis = .sexBased := by decide

/-- @cite{corbett-1991}'s key finding: no language assigns gender on a purely
    formal basis without any semantic core. In the sample, every gendered
    language has semantic assignment (alone or combined with formal). -/
theorem no_purely_formal_in_sample :
    ∀ p ∈ allProfiles,
      p.genderCount ≠ .none →
        p.assignment = .semanticOnly ∨ p.assignment = .semanticAndFormal := by
  decide

/-- All 3-gender systems in the sample use semantic + formal assignment.
    Sex-based 3-gender systems require formal correlates because the
    masculine/feminine/neuter distinction can't be determined by semantics
    alone. -/
theorem three_gender_always_formal :
    ∀ p ∈ allProfiles,
      p.genderCount = .three → p.assignment = .semanticAndFormal := by decide

/-- A gender system without any agreement is not a gender system — genders
    are precisely the categories that trigger agreement. -/
theorem gender_implies_agreement :
    ∀ p ∈ allProfiles,
      (p.genderCount ≠ .none → p.HasAgreement) ∧
      (p.genderCount = .none → ¬ p.HasAgreement) := by decide

-- ============================================================================
-- §4. Corbett's Agreement Hierarchy
-- ============================================================================

/-! @cite{corbett-1991}'s Agreement Hierarchy:
    attributive > predicate > relative pronoun > personal pronoun > verb. -/

/-- Verb agreement implies higher-target agreement in the sample (none of
    the languages agree only on verbs). -/
theorem agreement_hierarchy_verb_implies_higher :
    ∀ p ∈ allProfiles,
      .verb ∈ p.agreementTargets →
        .attributive ∈ p.agreementTargets ∨
        .predicate ∈ p.agreementTargets ∨
        .personalPronoun ∈ p.agreementTargets := by decide

/-- No language in the sample agrees only on verbs. -/
theorem no_verb_only_agreement :
    ∀ p ∈ allProfiles, p.agreementTargets ≠ [.verb] := by decide

/-- No gendered language in the sample has agreement only on personal
    pronouns: pronoun agreement always co-occurs with at least one other
    target. -/
theorem no_pronoun_only_agreement :
    ∀ p ∈ allProfiles,
      (p.genderCount ≠ .none ∧ .personalPronoun ∈ p.agreementTargets) →
        .attributive ∈ p.agreementTargets ∨
        .predicate ∈ p.agreementTargets ∨
        .verb ∈ p.agreementTargets := by decide

/-- Noun-class systems (5+) show agreement on more targets than smaller
    systems. In the sample, all noun-class systems agree on ≥4 of the 5
    target types. -/
theorem noun_class_rich_agreement :
    ∀ p ∈ allProfiles,
      p.IsNounClassSystem → p.agreementTargets.length ≥ 4 := by decide

-- ============================================================================
-- §5. Basis × count interactions
-- ============================================================================

/-- Non-sex-based systems in the sample have ≥4 genders. When gender is not
    organised around sex, the system tends to proliferate. -/
theorem non_sex_based_more_genders :
    ∀ p ∈ allProfiles, p.basis = .nonSexBased → p.rawGenderCount ≥ 4 := by decide

/-- Semantic-only assignment in the sample is restricted to non-sex-based
    systems. Sex-based systems typically have formal correlates. -/
theorem semantic_only_is_non_sex_based :
    ∀ p ∈ allProfiles,
      p.assignment = .semanticOnly → p.basis = .nonSexBased := by decide

/-- All sex-based systems in the sample use semantic + formal assignment. -/
theorem sex_based_always_formal :
    ∀ p ∈ allProfiles,
      p.basis = .sexBased → p.assignment = .semanticAndFormal := by decide

-- ============================================================================
-- §6. Canonical-gender notion
-- ============================================================================

/-- European languages in the sample (and Hindi-Urdu) all have canonical
    gender systems (sex-based, 2 or 3 genders, semantic + formal). -/
theorem canonical_gender_attested :
    french.IsCanonicalGender ∧ spanish.IsCanonicalGender ∧
    german.IsCanonicalGender ∧ russian.IsCanonicalGender ∧
    latin.IsCanonicalGender ∧ romanian.IsCanonicalGender ∧
    hindiUrdu.IsCanonicalGender := by decide

-- ============================================================================
-- §7. SurfaceGender bridge (post Bool→Prop migration)
-- ============================================================================

/-- Every 2- or 3-gender sex-based language in the sample exposes the
    appropriate `Features.SurfaceGender` values via the
    `attestedSurfaceGenders` bridge field. Connects the typology layer
    to the per-noun lexical layer. -/
theorem surface_gender_bridge_populated :
    ∀ p ∈ allProfiles,
      (p.genderCount = .two ∧ p.basis = .sexBased →
        p.attestedSurfaceGenders.length = 2) ∧
      (p.genderCount = .three ∧ p.basis = .sexBased →
        p.attestedSurfaceGenders.length = 3) := by decide

-- ============================================================================
-- §8. ISO code sanity (drift sentry)
-- ============================================================================

theorem iso_codes_unique :
    (allProfiles.map (·.iso639)).eraseDups.length = allProfiles.length := by
  decide

-- ============================================================================
-- §9. Within-Corbett (1991 vs 2013) divergence theorems
-- ============================================================================

/-! Three first-class disagreements between Corbett's 1991 monograph and
    his 2013 WALS chapters. The 1991 values are this Studies file's
    `english/dyirbal/georgian` overrides; the 2013 values are the
    Fragment-side `Fragments.{Lang}.Gender.genderTypology` (which goes
    through `GenderProfile.fromWALS`). Linglib's interconnection-density
    thesis: incompatibilities visible. -/

/-- Corbett 1991 vs 2013: English. The 1991 monograph applies a strict
    controller-marking criterion (English has none); the 2013 WALS chapter
    treats the *he/she/it* pronoun distinction as a 3-gender system. -/
theorem english_corbett1991_vs_corbett2013 :
    english.genderCount = .none ∧
    Fragments.English.Gender.genderTypology.genderCount = .three := by decide

/-- Corbett 1991 vs 2013: Dyirbal. The 1991 monograph treats Dyirbal as
    non-sex-based (organising principles cut across sex); the 2013 WALS
    chapter codes it as sex-based on the "Class I includes males"
    criterion. -/
theorem dyirbal_corbett1991_vs_corbett2013 :
    dyirbal.basis = .nonSexBased ∧
    Fragments.Dyirbal.Gender.genderTypology.basis = .sexBased := by decide

/-- Corbett 1991 vs 2013: Georgian. The 1991 monograph treats Georgian's
    rationality/animacy split as a 4-class gender system (agreement on
    pronouns + verbs); the 2013 WALS chapter codes it as no-gender on the
    noun-side-marking criterion. -/
theorem georgian_corbett1991_vs_corbett2013 :
    georgian.genderCount = .four ∧
    Fragments.Georgian.Gender.genderTypology.genderCount = .none := by decide

end Corbett1991
