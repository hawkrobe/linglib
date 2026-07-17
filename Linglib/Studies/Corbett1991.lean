import Linglib.Syntax.Agreement.Basic
import Linglib.Features.Gender.Basic
import Linglib.Data.WALS.Features.F30A
import Linglib.Data.WALS.Features.F31A
import Linglib.Data.WALS.Features.F32A

/-!
# Corbett (1991): Gender — typology of noun-class systems
[corbett-1991] [corbett-2013] [dryer-haspelmath-2013] [dixon-1972]

Greville Corbett. *Gender*. Cambridge University Press, 1991.
Plus [corbett-2013]'s WALS Chs 30, 31, 32.

This study file holds the 22-language exemplar sample and Corbett's
cross-linguistic generalisations over it. The per-language records
(`Profile`) live here — per-language paper-specific data belongs in the
study file that consumes it, not in Fragments. The WALS chapter values
are stored explicitly per language and *grounded* against
`Data.WALS.F30A/F31A/F32A` by the `*_wals_grounded` theorems; the
Ch 30 bin is derived from the controller-gender count
(`Profile.genderCount`), so bin/count consistency holds by construction.

## Deviations from earlier revisions

* The former `GenderProfile` substrate (`fromWALS` smart constructor with
  silent fallbacks, stored count + bin + consistency predicates) was
  dissolved into this file 2026-06-10.
* The former `IsCanonicalGender` predicate was renamed
  `IsPrototypicalSexBased`: "canonical gender" is [corbett-fedden-2016],
  whose Canonical Gender Principle makes *purely semantic* assignment
  canonical — the prototypical Indo-European mixed-assignment cell this
  predicate picks out is non-canonical in their sense.
* The former Dyirbal basis-override ("Corbett 1991 treats Dyirbal as
  non-sex-based") was dropped as unverifiable against the monograph:
  ch. 2 presents Dyirbal classes I/II as organised around male/female
  humans, which is WALS's sex-based criterion. The non-sex-based reading
  is Dixon/Lakoff framing and belongs to a study anchored on them.

## Sample composition

22 languages spanning all five WALS Ch 30 values: no gender (Mandarin,
Japanese, Turkish, Finnish, Korean, Quechua), 2 genders (French, Spanish,
Hindi-Urdu, Irish, Hebrew, Hausa), 3 genders (German, Russian, Latin,
Romanian, and — as a *pronominal* system — English), 4 genders (Dyirbal,
Archi), 5+ noun classes (Swahili, Zulu, Fula).
-/

set_option autoImplicit false

namespace Corbett1991

open Agreement (Target)
open Data.WALS

/-! ### Substrate: semantic bases and per-language profiles -/

/-- Semantic dimensions that can underlie gender / noun-class assignment.
    Editorial five-way cut over [corbett-1991]'s assignment discussion;
    consumed by [kramer-2020]'s Semantic Core Generalization. -/
inductive SemanticBasis where
  | sex
  | animacy
  | humanness
  | shape
  | rationality
  deriving DecidableEq, BEq, Repr

/-- A language's gender record for this study: the controller-gender
    count ([corbett-1991]'s ch. 6 counting — Swahili has 7 genders over
    ~15 traditional classes; Fula ~20), the WALS Ch 31/32 codings stored
    explicitly (grounded against `Data.WALS` below), agreement-target
    inventory, semantic bases, and the comparative-label bridge for
    sex-based systems. -/
structure Profile where
  name : String
  iso639 : String
  /-- Controller genders ([corbett-1991] ch. 6): sets of nouns taking the
      same agreements, with singular/plural pairings counted once. -/
  rawCount : Nat
  /-- WALS Ch 31 value ([corbett-2013]). -/
  basis : F31A.GenderBasis
  /-- WALS Ch 32 value ([corbett-2013]). -/
  assignment : F32A.SystemsOfGenderAssignment
  /-- Targets where gender agreement surfaces. An *inventory*, not the
      Agreement Hierarchy itself (which is a monotonicity claim about
      hybrid nouns; not yet formalized). -/
  agreementTargets : List Target := []
  /-- Semantic dimensions organising the system. -/
  semanticBases : List SemanticBasis := []
  /-- Comparative-label bridge for systems the
      `masculine/feminine/neuter/common` vocabulary covers; `[]` for
      noun-class systems (Bantu, Dyirbal). -/
  attestedGenders : List Gender := []
  deriving Repr, DecidableEq

namespace Profile

/-- WALS Ch 30 bin, derived from the controller-gender count. A count of
    1 maps to `.none`: one agreement pattern for all nouns is the absence
    of a system, not a one-gender system ([kramer-2015]'s two-class
    minimum; cf. `Gender.System`'s `Nontrivial` convention). -/
def genderCount (p : Profile) : F30A.GenderCount :=
  match p.rawCount with
  | 0 | 1 => .none
  | 2 => .two
  | 3 => .three
  | 4 => .four
  | _ => .fiveOrMore

/-- Whether the language has any gender agreement. -/
def HasAgreement (p : Profile) : Prop := p.agreementTargets ≠ []

instance : DecidablePred HasAgreement := fun p =>
  show Decidable (p.agreementTargets ≠ []) from inferInstance

/-- "Noun class" system: 5+ controller genders per [corbett-1991]'s
    conventional cut. -/
def IsNounClassSystem (p : Profile) : Prop := p.rawCount ≥ 5

instance : DecidablePred IsNounClassSystem := fun p =>
  show Decidable (p.rawCount ≥ 5) from inferInstance

/-- Internal coherence: a no-gender language has no-gender WALS codings
    and no agreement targets; a gendered one has gendered codings. -/
def IsCoherent (p : Profile) : Prop :=
  if p.rawCount = 0 then
    p.basis = .noGender ∧ p.assignment = .noGender ∧ p.agreementTargets = []
  else
    p.basis ≠ .noGender ∧ p.assignment ≠ .noGender

instance : DecidablePred IsCoherent := fun p =>
  decidable_of_iff
    (if p.rawCount = 0 then
      p.basis = .noGender ∧ p.assignment = .noGender ∧ p.agreementTargets = []
    else
      p.basis ≠ .noGender ∧ p.assignment ≠ .noGender)
    Iff.rfl

/-- Prototypical European-style gender system: sex-based, 2 or 3 genders,
    semantic + formal assignment.

    **Not** [corbett-fedden-2016]'s *canonical gender*: their Canonical
    Gender Principle makes purely semantic assignment canonical, so this
    mixed-assignment cell is non-canonical in their sense. The predicate
    picks out the prototypical Indo-European configuration. -/
def IsPrototypicalSexBased (p : Profile) : Prop :=
  (p.genderCount = .two ∨ p.genderCount = .three) ∧
  p.basis = .sexBased ∧
  p.assignment = .semanticAndFormal

instance : DecidablePred IsPrototypicalSexBased := fun p =>
  show Decidable (_ ∧ _ ∧ _) from inferInstance

/-! ### WALS grounding predicates

The stored Ch 30/31/32 values agree with `Data.WALS` wherever WALS covers
the language; for WALS-silent languages (Fula, Irish, Latin, Romanian)
the predicates hold vacuously and the stored value is this file's
commitment. -/

/-- Derived Ch 30 bin agrees with WALS F30A where covered. -/
def CountGrounded (p : Profile) : Prop :=
  ∀ d ∈ F30A.lookupISO p.iso639, d.value = p.genderCount

/-- Stored Ch 31 basis agrees with WALS F31A where covered. -/
def BasisGrounded (p : Profile) : Prop :=
  ∀ d ∈ F31A.lookupISO p.iso639, d.value = p.basis

/-- Stored Ch 32 assignment agrees with WALS F32A where covered. -/
def AssignmentGrounded (p : Profile) : Prop :=
  ∀ d ∈ F32A.lookupISO p.iso639, d.value = p.assignment

instance : DecidablePred CountGrounded := fun p =>
  show Decidable (∀ d ∈ F30A.lookupISO p.iso639, _) from inferInstance
instance : DecidablePred BasisGrounded := fun p =>
  show Decidable (∀ d ∈ F31A.lookupISO p.iso639, _) from inferInstance
instance : DecidablePred AssignmentGrounded := fun p =>
  show Decidable (∀ d ∈ F32A.lookupISO p.iso639, _) from inferInstance

end Profile

/-! ### The 22-language exemplar sample

Public (not `private`): [kramer-2020] and [carstens-2026] consume
individual profiles. -/

def english : Profile :=
  { name := "English", iso639 := "eng", rawCount := 3
  , basis := .sexBased, assignment := .semantic
  , agreementTargets := [.personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine, .neuter] }

def mandarin : Profile :=
  { name := "Mandarin Chinese", iso639 := "cmn", rawCount := 0
  , basis := .noGender, assignment := .noGender }

def japanese : Profile :=
  { name := "Japanese", iso639 := "jpn", rawCount := 0
  , basis := .noGender, assignment := .noGender }

def turkish : Profile :=
  { name := "Turkish", iso639 := "tur", rawCount := 0
  , basis := .noGender, assignment := .noGender }

def finnish : Profile :=
  { name := "Finnish", iso639 := "fin", rawCount := 0
  , basis := .noGender, assignment := .noGender }

def korean : Profile :=
  { name := "Korean", iso639 := "kor", rawCount := 0
  , basis := .noGender, assignment := .noGender }

def quechua : Profile :=
  { name := "Quechua (Cusco)", iso639 := "quz", rawCount := 0
  , basis := .noGender, assignment := .noGender }

def french : Profile :=
  { name := "French", iso639 := "fra", rawCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine] }

def spanish : Profile :=
  { name := "Spanish", iso639 := "spa", rawCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine] }

def hindiUrdu : Profile :=
  { name := "Hindi-Urdu", iso639 := "hin", rawCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .verb]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine] }

def irish : Profile :=
  { name := "Irish", iso639 := "gle", rawCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine] }

def hebrew : Profile :=
  { name := "Hebrew", iso639 := "heb", rawCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .verb]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine] }

def hausa : Profile :=
  { name := "Hausa", iso639 := "hau", rawCount := 2
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .personalPronoun, .verb]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine] }

def german : Profile :=
  { name := "German", iso639 := "deu", rawCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine, .neuter] }

def russian : Profile :=
  { name := "Russian", iso639 := "rus", rawCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verb]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine, .neuter] }

def latin : Profile :=
  { name := "Latin", iso639 := "lat", rawCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine, .neuter] }

def romanian : Profile :=
  { name := "Romanian", iso639 := "ron", rawCount := 3
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun]
  , semanticBases := [.sex]
  , attestedGenders := [.masculine, .feminine, .neuter] }

def dyirbal : Profile :=
  { name := "Dyirbal", iso639 := "dbl", rawCount := 4
  , basis := .sexBased, assignment := .semantic
  , agreementTargets := [.attributive]
  , semanticBases := [.sex, .animacy, .shape] }

/-- Archi. The stored assignment is this file's [corbett-1991] commitment
    (semantic *and formal*: the monograph documents phonological and
    morphological correlates for the gender III/IV split
    -- UNVERIFIED: locate the passage), diverging from WALS F32A's
    semantic-only coding — see `archi_corbett1991_vs_corbett2013`. -/
def archi : Profile :=
  { name := "Archi", iso639 := "aqc", rawCount := 4
  , basis := .sexBased, assignment := .semanticAndFormal
  , agreementTargets := [.predicate, .verb]
  , semanticBases := [.rationality, .sex, .animacy] }

def swahili : Profile :=
  { name := "Swahili", iso639 := "swh", rawCount := 7
  , basis := .nonSexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verb]
  , semanticBases := [.humanness, .animacy, .shape] }

def zulu : Profile :=
  { name := "Zulu", iso639 := "zul", rawCount := 8
  , basis := .nonSexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .relativePronoun,
                         .personalPronoun, .verb]
  , semanticBases := [.humanness, .animacy, .shape] }

def fula : Profile :=
  { name := "Fula", iso639 := "ful", rawCount := 20
  , basis := .nonSexBased, assignment := .semanticAndFormal
  , agreementTargets := [.attributive, .predicate, .personalPronoun, .verb]
  , semanticBases := [.humanness, .animacy, .shape] }

/-- All 22 language profiles in the Corbett 1991 sample. -/
def allProfiles : List Profile :=
  [ english, mandarin, japanese, turkish, finnish, korean, quechua
  , french, spanish, hindiUrdu, irish, hebrew, hausa
  , german, russian, latin, romanian
  , dyirbal, archi
  , swahili, zulu, fula ]

/-! ### WALS grounding -/

/-- Every derived Ch 30 bin agrees with WALS F30A where covered. -/
theorem count_wals_grounded :
    ∀ p ∈ allProfiles, p.CountGrounded := by decide

/-- Every stored Ch 31 basis agrees with WALS F31A where covered. -/
theorem basis_wals_grounded :
    ∀ p ∈ allProfiles, p.BasisGrounded := by decide

/-- Every stored Ch 32 assignment agrees with WALS F32A where covered —
    except Archi, whose 1991-vs-2013 divergence is first-class below. -/
theorem assignment_wals_grounded :
    ∀ p ∈ allProfiles, p.iso639 ≠ "aqc" → p.AssignmentGrounded := by decide

/-- Corbett 1991 vs 2013: Archi. The 1991 monograph treats assignment as
    semantic *and formal*; the 2013 WALS chapter (F32A) codes Archi as
    semantic-only. -/
theorem archi_corbett1991_vs_corbett2013 :
    archi.assignment = .semanticAndFormal ∧
    ∀ d ∈ F32A.lookupISO "aqc", d.value = .semantic := by decide

/-! ### Sample-level structural sanity -/

/-- All profiles are internally coherent. -/
theorem all_coherent :
    ∀ p ∈ allProfiles, p.IsCoherent := by decide

/-- All five WALS Ch 30 values are attested. -/
theorem all_gender_counts_attested :
    (∃ p ∈ allProfiles, p.genderCount = .none) ∧
    (∃ p ∈ allProfiles, p.genderCount = .two) ∧
    (∃ p ∈ allProfiles, p.genderCount = .three) ∧
    (∃ p ∈ allProfiles, p.genderCount = .four) ∧
    (∃ p ∈ allProfiles, p.genderCount = .fiveOrMore) := by decide

/-- All three Ch 31 values are attested. -/
theorem all_bases_attested :
    (∃ p ∈ allProfiles, p.basis = .noGender) ∧
    (∃ p ∈ allProfiles, p.basis = .sexBased) ∧
    (∃ p ∈ allProfiles, p.basis = .nonSexBased) := by decide

/-- All three Ch 32 values are attested. -/
theorem all_assignments_attested :
    (∃ p ∈ allProfiles, p.assignment = .noGender) ∧
    (∃ p ∈ allProfiles, p.assignment = .semantic) ∧
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
        p.assignment = .semantic ∨ p.assignment = .semanticAndFormal := by
  decide

/-- A gender system without any agreement is not a gender system — genders
    are precisely the categories that trigger agreement. -/
theorem gender_implies_agreement :
    ∀ p ∈ allProfiles,
      (p.genderCount ≠ .none → p.HasAgreement) ∧
      (p.genderCount = .none → ¬ p.HasAgreement) := by decide

/-! ### Agreement-target inventories

[corbett-1979] / [corbett-1991] ch. 8's Agreement Hierarchy has four
positions: attributive > predicate > relative pronoun > personal pronoun.
Verbal agreement (the substrate's `.verb` target, tested below) is
subsumed under the predicate position in Corbett's scheme.

The theorems below are *inventory* observations on the sample — which
targets mark gender at all. The hierarchy's actual content (monotone
availability of semantic agreement along the positions) is formalized
for number agreement in `Studies/Corbett2000.lean`
(`AgreementProfile.RespectsHierarchy`, with British English *committee*
as witness); the gender-side analogue for hybrid nouns like *vrač*
needs per-target assignment on `Gender.System.Assigned` and is still
open. -/

/-- Verb agreement implies higher-target agreement in the sample (none of
    the languages agree only on verbs). -/
theorem verb_agreement_implies_higher :
    ∀ p ∈ allProfiles,
      .verb ∈ p.agreementTargets →
        .attributive ∈ p.agreementTargets ∨
        .predicate ∈ p.agreementTargets ∨
        .personalPronoun ∈ p.agreementTargets := by decide

/-- No language in the sample agrees only on verbs. -/
theorem no_verb_only_agreement :
    ∀ p ∈ allProfiles, p.agreementTargets ≠ [.verb] := by decide

/-- English is the sample's pronominal gender system: it has gender
    (3 genders, *he/she/it*) but gender surfaces only on personal
    pronouns. -/
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

/-- Non-sex-based systems in the sample have ≥4 genders. When gender is
    not organised around sex, the system tends to proliferate. -/
theorem non_sex_based_more_genders :
    ∀ p ∈ allProfiles, p.basis = .nonSexBased → p.rawCount ≥ 4 := by decide

/-! ### Prototypical sex-based systems -/

/-- The European languages in the sample (and Hindi-Urdu) all instantiate
    the prototypical sex-based configuration. (See
    `Profile.IsPrototypicalSexBased` for why this is *not*
    [corbett-fedden-2016]'s canonical gender.) -/
theorem prototypical_sex_based_attested :
    french.IsPrototypicalSexBased ∧ spanish.IsPrototypicalSexBased ∧
    german.IsPrototypicalSexBased ∧ russian.IsPrototypicalSexBased ∧
    latin.IsPrototypicalSexBased ∧ romanian.IsPrototypicalSexBased ∧
    hindiUrdu.IsPrototypicalSexBased := by decide

/-! ### Gender bridge -/

/-- Every 2- or 3-gender sex-based language in the sample exposes the
    appropriate `Gender` comparative labels via `attestedGenders`. -/
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

end Corbett1991
