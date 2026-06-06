import Linglib.Features.Gender.Basic
import Linglib.Typology.Gender

/-!
# German Derivational Gender: *-schaft* and related suffixes
[kramer-2020] [kramer-2015]

German is a 3-gender language (masculine, feminine, neuter) where certain
derivational suffixes deterministically assign gender:

- *-schaft* → always feminine: *Freundschaft*, *Gesellschaft*,
  *Wissenschaft*
- *-heit*, *-keit* → always feminine: *Freiheit*, *Möglichkeit*
- *-ung* → always feminine: *Zeitung*, *Bildung*
- *-chen*, *-lein* → always neuter: *Mädchen*, *Büchlein*

## Theory-neutral data layer

The Fragment carries one empirical field per suffix: `assignedGender`,
the deterministic gender output. No `isNaturalGender` field —
derivational suffixes always assign arbitrary gender (the suffix is the
locus of the gender feature, not the root's semantic content). The
[kramer-2015] structural analysis (each suffix IS a categorizing
head *n* with a fixed gender feature: *-schaft* = n u[+FEM], *-chen* =
plain n) is a projection that lives in `Studies/`.

The empirical content captured here is the **morphological override**:
*Mädchen* 'girl' is neuter despite its semantic referent being female,
because the diminutive suffix *-chen* fixes the gender. This is
diagnostic for any theory in which suffixes can override semantics.
-/

namespace German.Gender


-- ============================================================================
-- § 1: Derivational Suffixes
-- ============================================================================

/-- A German derivational suffix that deterministically assigns gender.
    Theory-neutral: carries the empirical gender output, not a DM
    categorizing head. -/
structure DerivationalSuffix where
  form : String
  /-- Gender this suffix always assigns, regardless of the base. -/
  assignedGender : Gender
  deriving DecidableEq, Repr

def schaft : DerivationalSuffix := ⟨"-schaft", .feminine⟩
def heit   : DerivationalSuffix := ⟨"-heit",   .feminine⟩
def keit   : DerivationalSuffix := ⟨"-keit",   .feminine⟩
def ung    : DerivationalSuffix := ⟨"-ung",    .feminine⟩
def chen   : DerivationalSuffix := ⟨"-chen",   .neuter⟩
def lein   : DerivationalSuffix := ⟨"-lein",   .neuter⟩

-- ============================================================================
-- § 2: Derived Nouns
-- ============================================================================

/-- A German noun derived via a gender-assigning suffix. The noun's
    surface gender is the suffix's `assignedGender` (suffix overrides
    base semantics, e.g. *Mädchen*). -/
structure DerivedNoun where
  form : String
  gloss : String
  suffix : DerivationalSuffix
  deriving DecidableEq, Repr

namespace DerivedNoun

abbrev gender (n : DerivedNoun) : Gender := n.suffix.assignedGender

end DerivedNoun

-- -schaft nouns (all feminine)
def freundschaft  : DerivedNoun := ⟨"Freundschaft",  "friendship",   schaft⟩
def gesellschaft  : DerivedNoun := ⟨"Gesellschaft",  "society",      schaft⟩
def wissenschaft  : DerivedNoun := ⟨"Wissenschaft",  "science",      schaft⟩
def meisterschaft : DerivedNoun := ⟨"Meisterschaft", "championship", schaft⟩

-- -heit/-keit nouns (all feminine)
def freiheit      : DerivedNoun := ⟨"Freiheit",      "freedom",      heit⟩
def moeglichkeit  : DerivedNoun := ⟨"Möglichkeit",   "possibility",  keit⟩

-- -ung nouns (all feminine)
def zeitung       : DerivedNoun := ⟨"Zeitung",       "newspaper",    ung⟩
def bildung       : DerivedNoun := ⟨"Bildung",       "education",    ung⟩

-- -chen/-lein nouns (all neuter, even from feminine bases)
def maedchen      : DerivedNoun := ⟨"Mädchen",       "girl",         chen⟩
def buechlein     : DerivedNoun := ⟨"Büchlein",      "booklet",      lein⟩

def allDerived : List DerivedNoun :=
  [freundschaft, gesellschaft, wissenschaft, meisterschaft,
   freiheit, moeglichkeit, zeitung, bildung, maedchen, buechlein]

-- ============================================================================
-- § 3: Empirical observations
-- ============================================================================

/-- All *-schaft*, *-heit*, *-keit*, *-ung* derived nouns surface as
    feminine — the suffix deterministically assigns feminine. Stated
    directly over `assignedGender` (no DM intermediary). -/
theorem feminine_suffixes_assign_feminine :
    [freundschaft, gesellschaft, wissenschaft, meisterschaft,
     freiheit, moeglichkeit, zeitung, bildung].all
      (·.gender == .feminine) := by decide

/-- *-chen* and *-lein* derived nouns surface as neuter. -/
theorem diminutive_suffixes_assign_neuter :
    chen.assignedGender = .neuter ∧ lein.assignedGender = .neuter :=
  ⟨rfl, rfl⟩

/-- **Mädchen override**: *Mädchen* 'girl' is neuter despite its
    semantic referent being female. The diminutive suffix *-chen*
    overrides the natural-gender expectation — empirical fact that any
    theory must account for. The DM-specific analysis (suffix IS the n
    head, plain n → neuter via 3-gender VI) lives in
    `Studies/Kramer2020.lean`. -/
theorem maedchen_neuter_override :
    maedchen.gender = .neuter ∧ maedchen.gloss = "girl" := ⟨rfl, rfl⟩

-- ============================================================================
-- § 4: Typology profile (Corbett 1991, WALS Ch 30/31/32)
-- ============================================================================

open Typology.Gender

/-- German gender typology: 3-gender canonical sex-based. The derivational
    facts above (-schaft, -chen, etc.) are the formal-assignment evidence
    that justifies the WALS Ch 32 `semanticAndFormal` value. -/
def genderTypology : GenderProfile :=
  .fromWALS "German" "deu"
    (rawGenderCount := 3)
    (agreementTargets := [.attributive, .predicate, .relativePronoun, .personalPronoun])
    (semanticBases := [.sex])
    (attestedGenders := [.masculine, .feminine, .neuter])

theorem genderTypology_iso639 : genderTypology.iso639 = "deu" := rfl

theorem genderTypology_name : genderTypology.name = "German" := rfl

theorem isRawCountConsistent_genderTypology :
    genderTypology.IsRawCountConsistent := by decide

/-- German is in [corbett-1991]'s "canonical" cell. -/
theorem isCanonicalGender_genderTypology :
    genderTypology.IsCanonicalGender := by decide

end German.Gender
