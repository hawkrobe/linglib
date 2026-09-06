import Linglib.Fragments.Swahili.Basic
import Linglib.Syntax.Category.Noun.Basic

/-!
# Swahili nouns

Nouns carry a morphological class, the singular and plural prefixes they take, and a
controller gender, the class pair whose agreements they control; the two coincide for most
nouns but come apart for animates, which take class 1/2 agreements whatever their prefixes
([welmers-1973]; [corbett-1991]). Augmentatives and diminutives are formed by moving a stem
into class 5/6 or 7/8.

## References

* [W. E. Welmers, *African Language Structures* (1973)][welmers-1973]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

namespace Swahili

/-- Evaluative derivation by class change. -/
inductive Evaluative where
  | augmentative
  | diminutive
  deriving DecidableEq, Repr, Fintype

/-- A Swahili noun: its morphological class (the prefixes on the noun), the gender whose
agreements it controls, and whether it denotes an animate. -/
structure Noun extends GenderedNoun Gender where
  /-- The class pair whose prefixes the noun carries. -/
  morphClass : Gender
  /-- Whether the noun denotes an animate. -/
  animate : Bool
  /-- Augmentative or diminutive derivation, if any. -/
  evaluative : Option Evaluative := none
  deriving DecidableEq, Repr

def kikapu : Noun :=
  { form := "kikapu", gloss := "basket", morphClass := .genderD,
    gender := .genderD, animate := false }
def kiti : Noun :=
  { form := "kiti", gloss := "stool", morphClass := .genderD,
    gender := .genderD, animate := false }
def mti : Noun :=
  { form := "mti", gloss := "tree", morphClass := .genderB,
    gender := .genderB, animate := false }
def mguu : Noun :=
  { form := "mguu", gloss := "leg", morphClass := .genderB,
    gender := .genderB, animate := false }
def nyumba : Noun :=
  { form := "nyumba", gloss := "house", morphClass := .genderE,
    gender := .genderE, animate := false }
def mtu : Noun :=
  { form := "mtu", gloss := "person", morphClass := .genderA,
    gender := .genderA, animate := true }
def mwalimu : Noun :=
  { form := "mwalimu", gloss := "teacher", morphClass := .genderA,
    gender := .genderA, animate := true }
def mnyama : Noun :=
  { form := "mnyama", gloss := "animal", morphClass := .genderA,
    gender := .genderA, animate := true }
def mdudu : Noun :=
  { form := "mdudu", gloss := "insect", morphClass := .genderA,
    gender := .genderA, animate := true }
/-- *kifaru* 'rhinoceros': class 7 prefix, class 1/2 agreements. -/
def kifaru : Noun :=
  { form := "kifaru", gloss := "rhinoceros", morphClass := .genderD,
    gender := .genderA, animate := true }
/-- *kiboko* 'hippopotamus': class 7 prefix, class 1/2 agreements. -/
def kiboko : Noun :=
  { form := "kiboko", gloss := "hippopotamus", morphClass := .genderD,
    gender := .genderA, animate := true }
def mjusi : Noun :=
  { form := "mjusi", gloss := "lizard", morphClass := .genderB,
    gender := .genderA, animate := true }
def jogoo : Noun :=
  { form := "jogoo", gloss := "rooster", morphClass := .genderC,
    gender := .genderA, animate := true }
def kipofu : Noun :=
  { form := "kipofu", gloss := "blind person", morphClass := .genderD,
    gender := .genderA, animate := true }
def tembo : Noun :=
  { form := "tembo", gloss := "elephant", morphClass := .genderE,
    gender := .genderA, animate := true }
def nyoka : Noun :=
  { form := "nyoka", gloss := "snake", morphClass := .genderE,
    gender := .genderA, animate := true }
def rafiki : Noun :=
  { form := "rafiki", gloss := "friend", morphClass := .genderE,
    gender := .genderA, animate := true }
def ngombe : Noun :=
  { form := "ng'ombe", gloss := "cow", morphClass := .genderE,
    gender := .genderA, animate := true }
/-- *joka* 'giant snake', the augmentative of *nyoka*. -/
def joka : Noun :=
  { form := "joka", gloss := "giant snake", morphClass := .genderC,
    gender := .genderC, animate := true, evaluative := some .augmentative }
/-- *kitoto* 'baby', the diminutive of *mtoto* 'child'. -/
def kitoto : Noun :=
  { form := "kitoto", gloss := "baby", morphClass := .genderD,
    gender := .genderD, animate := true, evaluative := some .diminutive }
/-- *kijoka* 'tiny snake', the diminutive of *joka*. -/
def kijoka : Noun :=
  { form := "kijoka", gloss := "tiny snake", morphClass := .genderD,
    gender := .genderD, animate := true, evaluative := some .diminutive }

def allNouns : List Noun :=
  [kikapu, kiti, mti, mguu, nyumba, mtu, mwalimu, mnyama, mdudu, kifaru, kiboko, mjusi, jogoo,
    kipofu, tembo, nyoka, rafiki, ngombe, joka, kitoto, kijoka]

/-- Verbal subject agreement, singular and plural, distinguishes the five genders. -/
theorem faithful_subjPrefix :
    Gender.Faithful (λ (g : Gender) (pl : Bool) =>
      (if pl then g.pluralClass else g.singularClass).subjPrefix) := by
  decide

end Swahili
