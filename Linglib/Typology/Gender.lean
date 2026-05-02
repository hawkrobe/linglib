import Linglib.Core.Agreement.Target
import Linglib.Features.Gender
import Linglib.Datasets.WALS.Features.F30A
import Linglib.Datasets.WALS.Features.F31A
import Linglib.Datasets.WALS.Features.F32A

/-!
# Typology.Gender
@cite{corbett-1991} @cite{corbett-2013} @cite{dryer-haspelmath-2013}
@cite{dixon-1972} @cite{wals-2013}

Per-language typological substrate for gender / noun class systems. Covers
three WALS chapters by @cite{corbett-2013}:

- **Ch 30**: number of genders (none, 2, 3, 4, 5+).
- **Ch 31**: sex-based vs non-sex-based.
- **Ch 32**: systems of gender assignment (semantic only, semantic + formal).

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination,Modality}`
substrate-extension pattern. Fragment-importable.

## What lives here

- `GenderCount` (5-way), `GenderBasis` (3-way), `AssignmentSystem` (3-way),
  `SemanticBasis` (5-way) enums.
- `GenderProfile` per-language struct.
- WALS converters: `fromWALS30A`, `fromWALS31A`, `fromWALS32A`.
- Corpus-only generalisations from WALS Ch 30/31/32.
- Helper predicates (`rawCountConsistent`, `crossChapterConsistent`,
  `isNounClassSystem`, `hasAgreement`, `lowestAgreementTarget`,
  `isCanonicalGender`, `hasTarget`).

## Theory-laden caveats

- **`GenderCount.fivePlus` is a single bin** for systems with 5+ noun
  classes. The boundary between "gender" (2-3) and "noun class" (4+) is
  conventional, not categorical (@cite{corbett-1991}). Bantu languages
  with ~15 classes and Fula with ~20 are both `.fivePlus`.
- **`SemanticBasis` lists 5 dimensions** (sex, animacy, humanness, shape,
  rationality); other classifications (e.g. Aikhenvald 2003 noun-classifier
  semantics) cut differently.

## Out of scope

The 21-language sample and Corbett's typological generalisations live in
`Phenomena/Gender/Studies/Corbett1991.lean`.
@cite{kramer-2020}'s feature-tier analysis lives in
`Phenomena/Gender/Studies/Kramer2020.lean`.
-/

set_option autoImplicit false

namespace Typology.Gender

open Core (AgreementTarget)

private abbrev ch30 := Datasets.WALS.F30A.allData
private abbrev ch31 := Datasets.WALS.F31A.allData
private abbrev ch32 := Datasets.WALS.F32A.allData

-- ============================================================================
-- §1. Substrate enums
-- ============================================================================

/-- Number of gender / noun class distinctions in a language (WALS Ch 30). -/
inductive GenderCount where
  | none      -- no gender system
  | two       -- 2 genders (e.g. French masc/fem)
  | three     -- 3 genders (e.g. German masc/fem/neut)
  | four      -- 4 genders (e.g. Dyirbal)
  | fivePlus  -- 5+ genders / noun classes (e.g. Bantu)
  deriving DecidableEq, BEq, Repr

instance : Inhabited GenderCount := ⟨.none⟩

/-- Numeric lower bound for each `GenderCount` category. -/
def GenderCount.lowerBound : GenderCount → Nat
  | .none     => 0
  | .two      => 2
  | .three    => 3
  | .four     => 4
  | .fivePlus => 5

/-- Whether a raw gender count falls in a given `GenderCount` category. -/
def GenderCount.contains (gc : GenderCount) (n : Nat) : Bool :=
  match gc with
  | .none     => n == 0
  | .two      => n == 2
  | .three    => n == 3
  | .four     => n == 4
  | .fivePlus => n >= 5

/-- Whether a gender system is based on biological sex (WALS Ch 31). -/
inductive GenderBasis where
  | noGender
  | sexBased
  | nonSexBased
  deriving DecidableEq, BEq, Repr

instance : Inhabited GenderBasis := ⟨.noGender⟩

/-- How nouns are assigned to their gender categories (WALS Ch 32). -/
inductive AssignmentSystem where
  | noGender
  | semanticOnly
  | semanticAndFormal
  deriving DecidableEq, BEq, Repr

instance : Inhabited AssignmentSystem := ⟨.noGender⟩

/-- Semantic dimensions that can underlie gender / noun class assignment. -/
inductive SemanticBasis where
  | sex
  | animacy
  | humanness
  | shape
  | rationality
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2. GenderProfile (Fragment-side joint)
-- ============================================================================

/-- A language's gender profile combining WALS Chs 30/31/32 + extra fields
    (raw count, agreement targets per @cite{corbett-1991}'s Agreement
    Hierarchy, and semantic-basis dimensions). -/
structure GenderProfile where
  /-- Language name. -/
  name : String
  /-- ISO 639-3 code. -/
  iso639 : String
  /-- Ch 30: number of genders (WALS bin). -/
  genderCount : GenderCount
  /-- Actual number of gender / noun class categories. -/
  rawGenderCount : Nat
  /-- Ch 31: sex-based or non-sex-based. -/
  basis : GenderBasis
  /-- Ch 32: assignment system. -/
  assignment : AssignmentSystem
  /-- Where gender agreement surfaces (@cite{corbett-1991} Agreement
      Hierarchy: attributive > predicate > relative > pronoun > verb). -/
  agreementTargets : List AgreementTarget
  /-- Semantic dimensions organising the system. -/
  semanticBases : List SemanticBasis
  /-- Bridge to the lexical-layer `Features.SurfaceGender` taxonomy: the
      surface gender values attested in this language. Defaults to `[]` for
      noun-class systems (Bantu, Mixtec, Dyirbal) whose per-class agreement
      doesn't map onto the Indo-European `masculine/feminine/neuter/common`
      scheme; per-Fragment files for those languages retain a fine-grained
      `Gender` type and provide their own `Features.SurfaceGender` bridge
      via a `.primary` function. -/
  attestedSurfaceGenders : List Features.SurfaceGender := []
  deriving Repr, DecidableEq

-- ============================================================================
-- §3. Helper predicates
-- ============================================================================

/-- Whether the raw gender count is consistent with the WALS bin. -/
def GenderProfile.rawCountConsistent (p : GenderProfile) : Bool :=
  p.genderCount.contains p.rawGenderCount

/-- Whether the profile is internally consistent across chapters:
    no-gender in Ch 30 should align with `noGender` in Ch 31 and Ch 32. -/
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

/-- Lowest agreement target in @cite{corbett-1991}'s hierarchy. -/
def GenderProfile.lowestAgreementTarget (p : GenderProfile) :
    Option AgreementTarget :=
  p.agreementTargets.foldl
    (λ acc t => match acc with
      | none => some t
      | some prev => if t.rank < prev.rank then some t else some prev)
    none

/-- Whether a gender system is "canonical" in @cite{corbett-1991}'s sense:
    sex-based, with 2 or 3 genders, and semantic + formal assignment. -/
def GenderProfile.isCanonicalGender (p : GenderProfile) : Bool :=
  (p.genderCount == .two || p.genderCount == .three) &&
  p.basis == .sexBased &&
  p.assignment == .semanticAndFormal

/-- Whether a list of agreement targets contains a specific target. -/
def hasTarget (targets : List AgreementTarget) (t : AgreementTarget) : Bool :=
  targets.any (· == t)

-- ============================================================================
-- §4. WALS converters
-- ============================================================================

/-- WALS Ch 30A → `GenderCount`. -/
def fromWALS30A : Datasets.WALS.F30A.GenderCount → GenderCount
  | .none       => .none
  | .two        => .two
  | .three      => .three
  | .four       => .four
  | .fiveOrMore => .fivePlus

/-- WALS Ch 31A → `GenderBasis`. -/
def fromWALS31A : Datasets.WALS.F31A.GenderBasis → GenderBasis
  | .noGender    => .noGender
  | .sexBased    => .sexBased
  | .nonSexBased => .nonSexBased

/-- WALS Ch 32A → `AssignmentSystem`. -/
def fromWALS32A :
    Datasets.WALS.F32A.SystemsOfGenderAssignment → AssignmentSystem
  | .noGender          => .noGender
  | .semantic          => .semanticOnly
  | .semanticAndFormal => .semanticAndFormal

-- ============================================================================
-- §5. WALS Lookup Helpers + Smart Constructor
-- ============================================================================

def walsGenderCount (iso : String) : Option GenderCount :=
  (Datasets.WALS.F30A.lookupISO iso).map (fromWALS30A ·.value)

def walsGenderBasis (iso : String) : Option GenderBasis :=
  (Datasets.WALS.F31A.lookupISO iso).map (fromWALS31A ·.value)

def walsAssignment (iso : String) : Option AssignmentSystem :=
  (Datasets.WALS.F32A.lookupISO iso).map (fromWALS32A ·.value)

/-- Build a `GenderProfile` from an ISO 639-3 code via WALS lookups for
    Chs 30/31/32. The three required-field fallbacks (`genderCountFb`,
    `basisFb`, `assignmentFb`) fire only when WALS is silent for that ISO.
    The `rawGenderCount`, `agreementTargets`, `semanticBases`, and
    `attestedSurfaceGenders` fields are paper-stipulated per @cite{corbett-1991}
    — they are not derivable from any WALS chapter and must be passed
    explicitly. -/
def GenderProfile.fromWALS
    (name iso : String)
    (rawGenderCount : Nat)
    (agreementTargets : List AgreementTarget := [])
    (semanticBases : List SemanticBasis := [])
    (attestedSurfaceGenders : List Features.SurfaceGender := [])
    (genderCountFb : GenderCount := .none)
    (basisFb : GenderBasis := .noGender)
    (assignmentFb : AssignmentSystem := .noGender) : GenderProfile :=
  { name, iso639 := iso
  , genderCount := (walsGenderCount iso).getD genderCountFb
  , rawGenderCount
  , basis := (walsGenderBasis iso).getD basisFb
  , assignment := (walsAssignment iso).getD assignmentFb
  , agreementTargets
  , semanticBases
  , attestedSurfaceGenders }

-- ============================================================================
-- §6. Theory-neutral WALS distribution facts
-- ============================================================================

/-- Ch 30: languages with no gender are the modal category. -/
theorem ch30_no_gender_modal :
    let noGender := (ch30.filter (·.value == .none)).length
    noGender > (ch30.filter (·.value == .two)).length ∧
    noGender > (ch30.filter (·.value == .three)).length ∧
    noGender > (ch30.filter (·.value == .four)).length ∧
    noGender > (ch30.filter (·.value == .fiveOrMore)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Ch 30: among gender-bearing languages, 2-gender systems are most common. -/
theorem ch30_two_most_common :
    (ch30.filter (·.value == .two)).length >
    (ch30.filter (·.value == .three)).length ∧
    (ch30.filter (·.value == .two)).length >
    (ch30.filter (·.value == .four)).length ∧
    (ch30.filter (·.value == .two)).length >
    (ch30.filter (·.value == .fiveOrMore)).length := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Ch 31: sex-based systems far outnumber non-sex-based ones. -/
theorem ch31_sex_based_dominant :
    (ch31.filter (·.value == .sexBased)).length >
    (ch31.filter (·.value == .nonSexBased)).length := by native_decide

/-- Ch 32: semantic-and-formal assignment slightly outnumbers semantic-only. -/
theorem ch32_mixed_slightly_more :
    (ch32.filter (·.value == .semanticAndFormal)).length >
    (ch32.filter (·.value == .semantic)).length := by native_decide

/-- Ch 32: no purely-formal assignment system is attested. WALS F32A has only
    three categories: `noGender`, `semantic`, `semanticAndFormal`. -/
theorem ch32_no_purely_formal :
    ch32.all (λ d => d.value == .noGender || d.value == .semantic ||
                     d.value == .semanticAndFormal) := by native_decide

end Typology.Gender
