import Linglib.Features.Gender
import Linglib.Theories.Morphology.DM.Categorizer

/-!
# German Derivational Gender: *-schaft* and related suffixes
@cite{kramer-2020} @cite{kramer-2015}

German is a 3-gender language (masculine, feminine, neuter) where certain
derivational suffixes deterministically assign gender:

- *-schaft* → always feminine: *Freundschaft*, *Gesellschaft*, *Wissenschaft*
- *-heit*, *-keit* → always feminine: *Freiheit*, *Möglichkeit*
- *-ung* → always feminine: *Zeitung*, *Bildung*
- *-chen*, *-lein* → always neuter: *Mädchen*, *Büchlein*

Under @cite{kramer-2015}'s structural analysis, each suffix IS a
nominalizing head n with a fixed gender feature: *-schaft* = n u[+FEM],
*-chen* = n (plain n, neuter in 3-gender VI). The deterministic gender
follows from the feature on n, not from a phonological rule.
-/

namespace Fragments.German.Gender

open Morphology.DM (CatHead)
open Features (SurfaceGender)

-- ============================================================================
-- § 1: Derivational Suffixes as n Heads
-- ============================================================================

/-- German derivational suffixes that deterministically assign gender.
    Each suffix corresponds to a DM categorizing head n with fixed features. -/
structure DerivationalSuffix where
  form : String
  nHead : CatHead
  deriving Repr, BEq

def schaft : DerivationalSuffix := ⟨"-schaft", .n_uFem⟩
def heit   : DerivationalSuffix := ⟨"-heit",   .n_uFem⟩
def keit   : DerivationalSuffix := ⟨"-keit",   .n_uFem⟩
def ung    : DerivationalSuffix := ⟨"-ung",    .n_uFem⟩
def chen   : DerivationalSuffix := ⟨"-chen",   .n_plain⟩
def lein   : DerivationalSuffix := ⟨"-lein",   .n_plain⟩

-- ============================================================================
-- § 2: Derived Nouns
-- ============================================================================

/-- A German noun derived via a gender-assigning suffix. -/
structure DerivedNoun where
  form : String
  gloss : String
  suffix : DerivationalSuffix
  deriving Repr, BEq

-- -schaft nouns (all feminine)
def freundschaft   : DerivedNoun := ⟨"Freundschaft",   "friendship",  schaft⟩
def gesellschaft   : DerivedNoun := ⟨"Gesellschaft",   "society",     schaft⟩
def wissenschaft   : DerivedNoun := ⟨"Wissenschaft",   "science",     schaft⟩
def meisterschaft  : DerivedNoun := ⟨"Meisterschaft",  "championship",schaft⟩

-- -heit/-keit nouns (all feminine)
def freiheit       : DerivedNoun := ⟨"Freiheit",       "freedom",     heit⟩
def moeglichkeit   : DerivedNoun := ⟨"Möglichkeit",    "possibility", keit⟩

-- -ung nouns (all feminine)
def zeitung        : DerivedNoun := ⟨"Zeitung",        "newspaper",   ung⟩
def bildung        : DerivedNoun := ⟨"Bildung",        "education",   ung⟩

-- -chen/-lein nouns (all neuter, even from feminine bases)
def maedchen       : DerivedNoun := ⟨"Mädchen",        "girl",        chen⟩
def buechlein      : DerivedNoun := ⟨"Büchlein",       "booklet",     lein⟩

def allDerived : List DerivedNoun :=
  [freundschaft, gesellschaft, wissenschaft, meisterschaft,
   freiheit, moeglichkeit, zeitung, bildung, maedchen, buechlein]

-- ============================================================================
-- § 3: 3-Gender VI Verification
-- ============================================================================

/-- All *-schaft*, *-heit*, *-keit*, *-ung* nouns surface as feminine under
    3-gender VI, because their n head bears u[+FEM]. -/
theorem feminine_suffixes_derive_feminine :
    allDerived.all (fun n =>
      n.suffix.nHead == .n_uFem →
      n.suffix.nHead.surfaceGenderThree == .feminine) = true := by native_decide

/-- *-chen* and *-lein* nouns surface as neuter under 3-gender VI,
    because their n head is plain n (no gender feature → neuter). -/
theorem diminutive_derives_neuter :
    maedchen.suffix.nHead.surfaceGenderThree = .neuter ∧
    buechlein.suffix.nHead.surfaceGenderThree = .neuter := ⟨rfl, rfl⟩

/-- *Mädchen* 'girl' is neuter despite its semantics (human female)
    because the diminutive suffix *-chen* IS the n head, and plain n
    has no gender feature. The suffix overrides semantic gender — this
    is the DM prediction: it's the n head's features, not the root's
    semantics, that determine morphosyntactic gender. -/
theorem maedchen_neuter_override :
    maedchen.suffix.nHead = .n_plain ∧
    maedchen.suffix.nHead.surfaceGenderThree = .neuter := ⟨rfl, rfl⟩

end Fragments.German.Gender
