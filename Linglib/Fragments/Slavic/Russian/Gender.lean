import Linglib.Features.Gender
import Linglib.Typology.Gender

/-!
# Russian Noun Gender
@cite{wade-2020} @cite{corbett-1991} @cite{kramer-2020} @cite{kramer-2015}

Russian has three surface genders: masculine, feminine, neuter. Gender
is partly determined by the referent's biological sex (semantic core)
and partly by morphological declension class.

## Theory-neutral data layer

The Fragment carries empirical fields per entry:

- `attestedGender : SurfaceGender` — the agreement-trigger fact
  (verified against @cite{wade-2020}). Three values for Russian:
  masculine, feminine, neuter.
- `isNaturalGender : Bool` — whether the gender comes from the
  referent's biological sex.
- `declClass : Option DeclClass` — Russian-specific morphological
  classification (@cite{wade-2020}). Optional because semantic-core
  nouns get their gender from the referent, not morphology.

These fields suffice to project entries to @cite{kramer-2015} Ch. 7's
5-n DM analysis (projection in `Studies/Kramer2020.lean`); they also
support @cite{corbett-1991}'s controller-target classification directly.

## Hybrid nouns

*vrač* 'doctor' triggers feminine agreement on some targets (verb,
predicate adjective) when the referent is female, while retaining
masculine morphology (@cite{wade-2020}, e.g. "Врач обязана..." with
fem.-agreeing predicate; @cite{corbett-1991}). The Fragment encodes
*vrač*'s morphological gender (masculine, derived from Class I); the
hybrid agreement story lives in `Studies/Kramer2020.lean §7` via the
existing `russianVrac : HybridNoun` struct.

## Per-entry verification

Entries explicitly named in @cite{kramer-2015}: *otec*, *put'*, *vrač*.
All others are extrapolations from Kramer's framework, anchored on
@cite{wade-2020}'s declension and gender treatment + @cite{corbett-1991}'s
canonical 5-language sample. *kost'* (Class III feminine) verified at
Wade ≈ noun-declension tables; *put'* (Class III masculine, sole
exception) verified at Wade §6397; *znamja* (-мя neuter) is the textbook
Class III neuter group.
-/

namespace Fragments.Slavic.Russian.Gender

open Features (SurfaceGender)

-- ============================================================================
-- § 1: Declension Classes (@cite{wade-2020})
-- ============================================================================

/-- Russian declension classes. Gender correlates with class but neither
    fully determines the other (@cite{corbett-1991};
    @cite{kramer-2020} §2.3.2). -/
inductive DeclClass where
  | I    -- e.g. zakon 'law' (typically masculine)
  | II   -- e.g. škola 'school' (typically feminine)
  | III  -- e.g. kost' 'bone' (typically feminine; exceptions: put', znamja)
  | IV   -- remaining patterns (typically neuter)
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Russian Noun (theory-neutral schema)
-- ============================================================================

/-- A Russian noun. Empirical agreement-gender + natural-gender +
    optional declension class. No commitment to any specific theoretical
    framework — Kramer's DM categorizing head, Corbett's controller-target
    are projections in `Studies/`. -/
structure RussianNoun where
  form : String
  gloss : String
  /-- Empirical agreement-trigger fact (@cite{wade-2020}). -/
  attestedGender : SurfaceGender
  /-- True iff the gender comes from biological sex of the referent.
      For *vrač* 'doctor' (hybrid) the morphological gender is encoded
      here as masculine; the hybrid female-referent agreement lives in
      `Studies/Kramer2020.lean §7`. -/
  isNaturalGender : Bool
  /-- Optional declension class. Semantic-core nouns may omit since
      their gender is determined by the referent. -/
  declClass : Option DeclClass := none
  deriving DecidableEq, Repr

namespace RussianNoun

abbrev gender (n : RussianNoun) : SurfaceGender := n.attestedGender

end RussianNoun

-- ============================================================================
-- § 3: Semantic Core (@cite{kramer-2020} ex. 17)
-- ============================================================================

def otec   : RussianNoun :=
  { form := "otec",   gloss := "father",  attestedGender := .masculine, isNaturalGender := true }
def mat'   : RussianNoun :=
  { form := "mat'",   gloss := "mother",  attestedGender := .feminine,  isNaturalGender := true }
def brat   : RussianNoun :=
  { form := "brat",   gloss := "brother", attestedGender := .masculine, isNaturalGender := true }
def sestra : RussianNoun :=
  { form := "sestra", gloss := "sister",  attestedGender := .feminine,  isNaturalGender := true }
def byk    : RussianNoun :=
  { form := "byk",    gloss := "bull",    attestedGender := .masculine, isNaturalGender := true }
def korova : RussianNoun :=
  { form := "korova", gloss := "cow",     attestedGender := .feminine,  isNaturalGender := true }

-- ============================================================================
-- § 4: Remainder — Declension-Class Correlation (@cite{kramer-2020} ex. 18)
-- ============================================================================

def zakon : RussianNoun :=
  { form := "zakon", gloss := "law",    attestedGender := .masculine
  , isNaturalGender := false, declClass := some .I }
def škola : RussianNoun :=
  { form := "škola", gloss := "school", attestedGender := .feminine
  , isNaturalGender := false, declClass := some .II }
def kost' : RussianNoun :=
  { form := "kost'", gloss := "bone",   attestedGender := .feminine
  , isNaturalGender := false, declClass := some .III }
def vino  : RussianNoun :=
  { form := "vino",  gloss := "wine",   attestedGender := .neuter
  , isNaturalGender := false, declClass := some .IV }

-- ============================================================================
-- § 5: Class III Exceptions (@cite{kramer-2020} ex. 19)
-- ============================================================================

/-- *znamja* 'banner': Class III but neuter, not feminine (the -мя
    neuter group; @cite{corbett-1991}; @cite{kramer-2020} ex. 19a). -/
def znamja : RussianNoun :=
  { form := "znamja", gloss := "banner", attestedGender := .neuter
  , isNaturalGender := false, declClass := some .III }

/-- *put'* 'way': the only masculine noun in Class III
    (@cite{wade-2020} §6397: "путь is qualified by masculine adjectives";
    @cite{corbett-1991}; @cite{kramer-2020} ex. 19b). -/
def put'   : RussianNoun :=
  { form := "put'", gloss := "way", attestedGender := .masculine
  , isNaturalGender := false, declClass := some .III }

-- ============================================================================
-- § 6: Hybrid Noun (@cite{kramer-2020} ex. 15–16)
-- ============================================================================

/-- *vrač* 'doctor': morphologically masculine (Class I), but triggers
    feminine agreement on some targets when the referent is female
    (verified at @cite{wade-2020} "Врач обязана…" with feminine-agreeing
    predicate). The Fragment encodes morphological gender; the hybrid
    behavior is captured in `Studies/Kramer2020.lean §7`. -/
def vrač : RussianNoun :=
  { form := "vrač", gloss := "doctor", attestedGender := .masculine
  , isNaturalGender := false, declClass := some .I }

-- ============================================================================
-- § 7: Inventory
-- ============================================================================

def semanticCoreNouns : List RussianNoun :=
  [otec, mat', brat, sestra, byk, korova]

def remainderNouns : List RussianNoun :=
  [zakon, škola, kost', vino, znamja, put']

def allNouns : List RussianNoun :=
  semanticCoreNouns ++ remainderNouns ++ [vrač]

-- ============================================================================
-- § 8: Cross-class observation
-- ============================================================================

/-- Declension class does not determine gender: *znamja* and *kost'*
    share Class III but differ in surface gender (the Class III
    counter-correlation @cite{corbett-1991} highlights). Stated
    directly over `attestedGender` (no DM intermediary). -/
theorem declClass_ne_gender :
    znamja.declClass = kost'.declClass ∧
    znamja.attestedGender ≠ kost'.attestedGender := ⟨rfl, by decide⟩

-- ============================================================================
-- § 9: Typology profile (Corbett 1991, WALS Ch 30/31/32)
-- ============================================================================

open Typology.Gender
open Core (AgreementTarget)

/-- Russian gender typology: 3-gender canonical sex-based with verb
    agreement (past tense). The declension classes above (I/II/III/IV)
    plus the §8 `declClass_ne_gender` theorem are the Class-vs-Gender
    independence evidence behind the WALS Ch 32 `semanticAndFormal` value. -/
def genderTypology : GenderProfile :=
  .fromWALS "Russian" "rus"
    (rawGenderCount := 3)
    (genderCountFb := .three)
    (basisFb := .sexBased)
    (assignmentFb := .semanticAndFormal)
    (agreementTargets := [.attributive, .predicate, .relativePronoun,
                          .personalPronoun, .verb])
    (semanticBases := [.sex])
    (attestedSurfaceGenders := [.masculine, .feminine, .neuter])

example : genderTypology.iso639 = "rus" ∧ genderTypology.name = "Russian" :=
  ⟨rfl, rfl⟩

end Fragments.Slavic.Russian.Gender
