import Linglib.Features.Gender.Profile
import Linglib.Syntax.Agreement.Basic
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
import Linglib.Fragments.Archi.Gender
import Linglib.Fragments.Swahili.Gender
import Linglib.Fragments.Zulu.Gender
import Linglib.Fragments.Fula.Gender

/-!
# Corbett (1991): Gender — typology of noun-class systems
[corbett-1991] [corbett-2013] [dryer-haspelmath-2013]
[dixon-1972]

Greville Corbett. *Gender*. Cambridge University Press, 1991.
Plus [corbett-2013]'s WALS Chs 30, 31, 32.

This study file holds Corbett's cross-linguistic generalisations on the
22-language sample. Per-language profiles live in
`Fragments/{Lang}/Gender.lean` as `genderTypology : GenderProfile` —
constructed via `GenderProfile.fromWALS` so WALS Chs 30/31/32 are
auto-pulled and the editorial fields (rawGenderCount, agreementTargets,
semanticBases, attestedGenders) are local per-language commitments.

## Sample composition

22 languages chosen to span all five `GenderCount` values:
- **No gender** (Mandarin, Japanese, Turkish, Finnish, Korean, Quechua —
  6 languages).
- **2 genders** (French, Spanish, Hindi-Urdu, Irish, Hebrew, Hausa —
  6 languages).
- **3 genders** (German, Russian, Latin, Romanian, and — as a *pronominal*
  gender system — English — 5 languages).
- **4 genders** (Dyirbal, Archi — 2 languages).
- **5+ noun classes** (Swahili, Zulu, Fula — 3 languages).

The sample includes Bantu noun-class systems (Swahili, Zulu) and Fula
(~20 genders), the Australian 4-class system Dyirbal, and the
Nakh-Daghestanian 4-gender system Archi (sex-based at the rational tier,
non-rational genders by animacy), alongside the canonical European
sex-based 2/3 systems and English's pronominal gender.

## What this file deliberately omits

Aggregate-count theorems (`sample_X_count = N`, `gender_scale_range`,
`sample_diversity`) — these go stale every time a Fragment is added to
the sample and were the "aggregate-count theorems" anti-pattern. The
substantive Corbett 1991 generalisations (the no-purely-formal-assignment
finding, Agreement Hierarchy properties, the canonical-gender notion) are
kept; ISO sanity remains as a drift sentry.
-/

set_option autoImplicit false

namespace Corbett1991

open _root_.Gender
open Agreement (AgreementTarget)

/-! ### The 22-language exemplar sample -/

/-! Per-language profiles drawn from `Fragments/{Lang}/Gender.lean` via
    `GenderProfile.fromWALS`. Aliases here for concise reference below.

    Two languages (Dyirbal, Archi) are record-updated to match Corbett's
    1991 monograph where it diverges from his later WALS chapters
    [corbett-2013]. The divergences are first-class theorems below —
    exposing them rather than hiding them inside the Fragment. -/

private abbrev english   := English.Gender.genderTypology
private abbrev mandarin  := Mandarin.Gender.genderTypology
private abbrev japanese  := Japanese.Gender.genderTypology
private abbrev turkish   := Turkish.Gender.genderTypology
private abbrev finnish   := Finnish.Gender.genderTypology
private abbrev korean    := Korean.Gender.genderTypology
private abbrev quechua   := Quechua.Gender.genderTypology
private abbrev french    := French.Gender.genderTypology
private abbrev spanish   := Spanish.Gender.genderTypology
private abbrev hindiUrdu := Hindi.Gender.genderTypology
private abbrev irish     := Irish.Gender.genderTypology
private abbrev hebrew    := Hebrew.Gender.genderTypology
private abbrev hausa     := Hausa.Gender.genderTypology
private abbrev german    := German.Gender.genderTypology
private abbrev russian   := Russian.Gender.genderTypology
private abbrev latin     := Latin.Gender.genderTypology
private abbrev romanian  := Romanian.Gender.genderTypology
private abbrev swahili   := Swahili.Gender.genderTypology
private abbrev zulu      := Zulu.Gender.genderTypology
private abbrev fula      := Fula.Gender.genderTypology

/-! Corbett-1991 record-overrides for the 2 languages where Corbett's 1991
    book disagrees with his 2013 WALS chapters. -/

/-- Corbett 1991: Dyirbal is 4-class non-sex-based (the system's organising
    criteria cut across biological sex). WALS [corbett-2013] F31A says
    sex-based on the narrow "Class I includes males" criterion. Override. -/
private def dyirbal : GenderProfile :=
  { Dyirbal.Gender.genderTypology with
    basis := .nonSexBased }

/-- Corbett 1991: Archi assignment is semantic *and formal* — the monograph
    documents phonological/morphological correlates for the gender III/IV
    split. WALS [corbett-2013] F32A codes Archi as semantic-only.
    Override the assignment; count/basis/targets agree with WALS. -/
private def archi : GenderProfile :=
  { Archi.Gender.genderTypology with
    assignment := .semanticAndFormal }

/-- All 22 language profiles in the Corbett 1991 sample. Dyirbal and Archi
    are the record-overridden versions (the WALS originals are at
    `Fragments.{Dyirbal,Archi}.Gender.genderTypology`); every other language,
    including English, uses its WALS-derived Fragment value directly. -/
def allProfiles : List GenderProfile :=
  [ english, mandarin, japanese, turkish, finnish, korean, quechua
  , french, spanish, hindiUrdu, irish, hebrew, hausa
  , german, russian, latin, romanian
  , dyirbal, archi
  , swahili, zulu, fula ]

/-! ### Sample-level structural sanity -/

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

/-! ### Cross-linguistic generalisations -/

/-- All 2- and 3-gender systems in the sample are sex-based. Reflects the
    cross-linguistic pattern that small gender systems organise around sex. -/
theorem two_three_gender_all_sex_based :
    ∀ p ∈ allProfiles,
      p.genderCount = .two ∨ p.genderCount = .three →
        p.basis = .sexBased := by decide

/-- [corbett-1991]'s key finding: no language assigns gender on a purely
    formal basis without any semantic core. In the sample, every gendered
    language has semantic assignment (alone or combined with formal). -/
theorem no_purely_formal_in_sample :
    ∀ p ∈ allProfiles,
      p.genderCount ≠ .none →
        p.assignment = .semanticOnly ∨ p.assignment = .semanticAndFormal := by
  decide

/-- A gender system without any agreement is not a gender system — genders
    are precisely the categories that trigger agreement. -/
theorem gender_implies_agreement :
    ∀ p ∈ allProfiles,
      (p.genderCount ≠ .none → p.HasAgreement) ∧
      (p.genderCount = .none → ¬ p.HasAgreement) := by decide

/-! ### Corbett's Agreement Hierarchy -/

/-! [corbett-1991]'s Agreement Hierarchy has four positions:
    attributive > predicate > relative pronoun > personal pronoun.
    Verbal agreement (the substrate's `.verb` `AgreementTarget`, tested
    below) is subsumed under the predicate position in Corbett's scheme. -/

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

/-- English is the sample's pronominal gender system: it has gender
    (3 genders, *he/she/it*) but gender surfaces only on personal pronouns —
    the canonical case of a system whose agreement sits at the low end of
    [corbett-1991]'s hierarchy. -/
theorem english_pronominal_gender :
    english.genderCount ≠ .none ∧
    english.agreementTargets = [.personalPronoun] := by decide

/-- Noun-class systems (5+) show agreement on more targets than smaller
    systems. In the sample, all noun-class systems agree on ≥4 of the 5
    target types. -/
theorem noun_class_rich_agreement :
    ∀ p ∈ allProfiles,
      p.IsNounClassSystem → p.agreementTargets.length ≥ 4 := by decide

/-! ### Basis × count interactions -/

/-- Non-sex-based systems in the sample have ≥4 genders. When gender is not
    organised around sex, the system tends to proliferate. -/
theorem non_sex_based_more_genders :
    ∀ p ∈ allProfiles, p.basis = .nonSexBased → p.rawGenderCount ≥ 4 := by decide

/-! ### Canonical-gender notion -/

/-- European languages in the sample (and Hindi-Urdu) all have canonical
    gender systems (sex-based, 2 or 3 genders, semantic + formal). -/
theorem canonical_gender_attested :
    french.IsCanonicalGender ∧ spanish.IsCanonicalGender ∧
    german.IsCanonicalGender ∧ russian.IsCanonicalGender ∧
    latin.IsCanonicalGender ∧ romanian.IsCanonicalGender ∧
    hindiUrdu.IsCanonicalGender := by decide

/-! ### Gender bridge -/

/-- Every 2- or 3-gender sex-based language in the sample exposes the
    appropriate `Gender` values via the
    `attestedGenders` bridge field. Connects the typology layer
    to the per-noun lexical layer. -/
theorem surface_gender_bridge_populated :
    ∀ p ∈ allProfiles,
      (p.genderCount = .two ∧ p.basis = .sexBased →
        p.attestedGenders.length = 2) ∧
      (p.genderCount = .three ∧ p.basis = .sexBased →
        p.attestedGenders.length = 3) := by decide

/-! ### ISO code sanity (drift sentry) -/

theorem iso_codes_unique :
    (allProfiles.map (·.iso639)).eraseDups.length = allProfiles.length := by
  decide

/-! ### Within-Corbett (1991 vs 2013) divergence theorems -/

/-! Two first-class disagreements between Corbett's 1991 monograph and his
    2013 WALS chapters. The 1991 values are this Studies file's `dyirbal`
    and `archi` overrides; the 2013 values are the Fragment-side
    `Fragments.{Lang}.Gender.genderTypology` (which goes through
    `GenderProfile.fromWALS`). Linglib's interconnection-density thesis:
    incompatibilities visible. -/

/-- Corbett 1991 vs 2013: Dyirbal. The 1991 monograph treats Dyirbal as
    non-sex-based (organising principles cut across sex); the 2013 WALS
    chapter codes it as sex-based on the "Class I includes males"
    criterion. -/
theorem dyirbal_corbett1991_vs_corbett2013 :
    dyirbal.basis = .nonSexBased ∧
    Dyirbal.Gender.genderTypology.basis = .sexBased := by decide

/-- Corbett 1991 vs 2013: Archi. The 1991 monograph documents phonological
    and morphological correlates for the gender III/IV split, so it treats
    assignment as semantic *and formal*; the 2013 WALS chapter (F32A) codes
    Archi as semantic assignment only. -/
theorem archi_corbett1991_vs_corbett2013 :
    archi.assignment = .semanticAndFormal ∧
    Archi.Gender.genderTypology.assignment = .semanticOnly := by decide

end Corbett1991
