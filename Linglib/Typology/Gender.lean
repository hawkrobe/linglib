import Linglib.Syntax.Agreement.Basic
import Linglib.Features.Gender
import Linglib.Data.WALS.Features.F30A
import Linglib.Data.WALS.Features.F31A
import Linglib.Data.WALS.Features.F32A

/-!
# Typology.Gender
[corbett-1991] [corbett-2013] [dryer-haspelmath-2013]
[dixon-1972] [wals-2013]

Per-language typological substrate for gender / noun class systems. Covers
three WALS chapters by [corbett-2013]:

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

- **`GenderCount.fivePlus` is a single bin** for systems with 5+ genders.
  The boundary between "gender" (2-3) and "noun class" (4+) is
  conventional, not categorical ([corbett-1991]). Raw counts are
  controller genders, not morphological classes: Swahili has 7 genders
  over ~15 traditional noun classes; Fula has ~20 genders.
- **`SemanticBasis` lists 5 dimensions** (sex, animacy, humanness, shape,
  rationality); other classifications (e.g. Aikhenvald 2003 noun-classifier
  semantics) cut differently.

## Out of scope

The 21-language sample and Corbett's typological generalisations live in
`Studies/Corbett1991.lean`.
[kramer-2020]'s feature-tier analysis lives in
`Studies/Kramer2020.lean`.
-/

set_option autoImplicit false

namespace Typology.Gender

open Agreement (AgreementTarget)

private abbrev ch30 := Data.WALS.F30A.allData
private abbrev ch31 := Data.WALS.F31A.allData
private abbrev ch32 := Data.WALS.F32A.allData

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
def GenderCount.Contains (gc : GenderCount) (n : Nat) : Prop :=
  match gc with
  | .none     => n = 0
  | .two      => n = 2
  | .three    => n = 3
  | .four     => n = 4
  | .fivePlus => n ≥ 5

instance (gc : GenderCount) (n : Nat) : Decidable (gc.Contains n) := by
  cases gc <;> unfold GenderCount.Contains <;> infer_instance

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
    (raw count, agreement targets per [corbett-1991]'s Agreement
    Hierarchy, and semantic-basis dimensions). -/
structure GenderProfile where
  /-- Language name. -/
  name : String
  /-- ISO 639-3 code. -/
  iso639 : String
  /-- Ch 30: number of genders (WALS bin). -/
  genderCount : GenderCount
  /-- Number of controller genders: sets of nouns taking the same
      agreements, typically singular/plural pairings ([corbett-1991] §6.3).
      For Bantu this counts genders like 1/2 — *not* the larger
      traditional noun-class inventory (Swahili: 7 genders, ~15 classes). -/
  rawGenderCount : Nat
  /-- Ch 31: sex-based or non-sex-based. -/
  basis : GenderBasis
  /-- Ch 32: assignment system. -/
  assignment : AssignmentSystem
  /-- Where gender agreement surfaces. [corbett-1991]'s Agreement
      Hierarchy has four positions (attributive > predicate > relative
      pronoun > personal pronoun); `verb` is a linglib refinement for
      verbal agreement (see `Agreement.AgreementTarget`). -/
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

namespace GenderProfile

/-! Mathlib-style `Prop`-typed predicates with `Decidable` instances and
    `@[simp] _iff` lemmas. Filter sites that need `Bool` should call
    `decide` at the boundary. -/

def IsRawCountConsistent (p : GenderProfile) : Prop :=
  p.genderCount.Contains p.rawGenderCount
@[simp] theorem isRawCountConsistent_iff (p : GenderProfile) :
    p.IsRawCountConsistent ↔ p.genderCount.Contains p.rawGenderCount := Iff.rfl
instance : DecidablePred IsRawCountConsistent :=
  fun p => decidable_of_iff _ (isRawCountConsistent_iff p).symm

/-- Internal consistency across WALS chapters: no-gender in Ch 30 aligns with
    `noGender` in Ch 31, Ch 32, and an empty agreement-target list. -/
def IsCrossChapterConsistent (p : GenderProfile) : Prop :=
  if p.genderCount = .none then
    p.basis = .noGender ∧ p.assignment = .noGender ∧
    p.agreementTargets = []
  else
    p.basis ≠ .noGender ∧ p.assignment ≠ .noGender
@[simp] theorem isCrossChapterConsistent_iff (p : GenderProfile) :
    p.IsCrossChapterConsistent ↔
      (if p.genderCount = .none then
        p.basis = .noGender ∧ p.assignment = .noGender ∧
        p.agreementTargets = []
      else
        p.basis ≠ .noGender ∧ p.assignment ≠ .noGender) := Iff.rfl
instance : DecidablePred IsCrossChapterConsistent := fun p =>
  show Decidable
      (if p.genderCount = .none then
        p.basis = .noGender ∧ p.assignment = .noGender ∧
        p.agreementTargets = []
      else
        p.basis ≠ .noGender ∧ p.assignment ≠ .noGender) from
    inferInstance

/-- "Noun class" system: 5+ categories per [corbett-1991]. -/
def IsNounClassSystem (p : GenderProfile) : Prop := p.rawGenderCount ≥ 5
@[simp] theorem isNounClassSystem_iff (p : GenderProfile) :
    p.IsNounClassSystem ↔ p.rawGenderCount ≥ 5 := Iff.rfl
instance : DecidablePred IsNounClassSystem :=
  fun p => decidable_of_iff _ (isNounClassSystem_iff p).symm

/-- Whether the language has any gender agreement. -/
def HasAgreement (p : GenderProfile) : Prop := p.agreementTargets ≠ []
@[simp] theorem hasAgreement_iff (p : GenderProfile) :
    p.HasAgreement ↔ p.agreementTargets ≠ [] := Iff.rfl
instance : DecidablePred HasAgreement :=
  fun p => decidable_of_iff _ (hasAgreement_iff p).symm

/-- "Canonical" gender system in [corbett-1991]'s sense: sex-based,
    2 or 3 genders, semantic + formal assignment. -/
def IsCanonicalGender (p : GenderProfile) : Prop :=
  (p.genderCount = .two ∨ p.genderCount = .three) ∧
  p.basis = .sexBased ∧
  p.assignment = .semanticAndFormal
@[simp] theorem isCanonicalGender_iff (p : GenderProfile) :
    p.IsCanonicalGender ↔
      (p.genderCount = .two ∨ p.genderCount = .three) ∧
      p.basis = .sexBased ∧
      p.assignment = .semanticAndFormal := Iff.rfl
instance : DecidablePred IsCanonicalGender := fun p =>
  show Decidable
      ((p.genderCount = .two ∨ p.genderCount = .three) ∧
       p.basis = .sexBased ∧
       p.assignment = .semanticAndFormal) from
    inferInstance

/-- Lowest agreement target in [corbett-1991]'s hierarchy. -/
def lowestAgreementTarget (p : GenderProfile) : Option AgreementTarget :=
  p.agreementTargets.foldl
    (λ acc t => match acc with
      | none => some t
      | some prev => if t.rank < prev.rank then some t else some prev)
    none

end GenderProfile

-- ============================================================================
-- §4. WALS converters
-- ============================================================================

/-- WALS Ch 30A → `GenderCount`. -/
def fromWALS30A : Data.WALS.F30A.GenderCount → GenderCount
  | .none       => .none
  | .two        => .two
  | .three      => .three
  | .four       => .four
  | .fiveOrMore => .fivePlus

/-- WALS Ch 31A → `GenderBasis`. -/
def fromWALS31A : Data.WALS.F31A.GenderBasis → GenderBasis
  | .noGender    => .noGender
  | .sexBased    => .sexBased
  | .nonSexBased => .nonSexBased

/-- WALS Ch 32A → `AssignmentSystem`. -/
def fromWALS32A :
    Data.WALS.F32A.SystemsOfGenderAssignment → AssignmentSystem
  | .noGender          => .noGender
  | .semantic          => .semanticOnly
  | .semanticAndFormal => .semanticAndFormal

-- ============================================================================
-- §5. WALS Lookup Helpers + Smart Constructor
-- ============================================================================

def walsGenderCount (iso : String) : Option GenderCount :=
  (Data.WALS.F30A.lookupISO iso).map (fromWALS30A ·.value)

def walsGenderBasis (iso : String) : Option GenderBasis :=
  (Data.WALS.F31A.lookupISO iso).map (fromWALS31A ·.value)

def walsAssignment (iso : String) : Option AssignmentSystem :=
  (Data.WALS.F32A.lookupISO iso).map (fromWALS32A ·.value)

/-- Build a `GenderProfile` from an ISO 639-3 code via WALS lookups for
    Chs 30/31/32. The three required-field fallbacks (`genderCountFb`,
    `basisFb`, `assignmentFb`) fire only when WALS is silent for that ISO.
    The `rawGenderCount`, `agreementTargets`, `semanticBases`, and
    `attestedSurfaceGenders` fields are paper-stipulated per [corbett-1991]
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
-- §6. WALS distribution facts
-- ============================================================================

/-! Earlier revisions of this file carried five aggregate-count theorems on
    the full WALS Ch 30/31/32 corpora (`ch30_no_gender_modal`,
    `ch30_two_most_common`, `ch31_sex_based_dominant`,
    `ch32_mixed_slightly_more`, `ch32_no_purely_formal`). These were the
    "aggregate-count theorems go stale" anti-pattern AND required
    `native_decide` for ~1000-element list reductions; deleted as part of
    the GenderProfile mathlib polish. The corpus distributions remain
    documentary in [corbett-2013]'s WALS chapters. -/

end Typology.Gender
