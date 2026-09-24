module

public import Linglib.Fragments.Swahili.Basic
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Swahili nouns

This file defines the Swahili nouns of Corbett's account of gender assignment. A noun carries
a morphological class, the pair of classes whose prefixes it takes, and a controller gender,
the pair of classes whose agreements it controls. The two coincide for most nouns and come
apart for animates, which take the agreements of classes 1 and 2 whatever their prefix, as
*kifaru* 'rhinoceros' with the prefix of class 7 and *tembo* 'elephant' with none. An
augmentative moves a stem into classes 5/6 and a diminutive into 7/8, *joka* 'giant snake'
and *kijoka* 'tiny snake' from *nyoka* 'snake'; the assignment rules that read these off are in
`Studies/Corbett1991.lean`.

## Main definitions

* `Swahili.Noun`: a noun with its morphological class, its animacy and its evaluative
  derivation
* `Swahili.allNouns`: the nouns of Corbett's examples and rules

## References

* [G. G. Corbett, *Gender* (1991)][corbett-1991]
-/

@[expose] public section

namespace Swahili

/-- An evaluative derivation moves a stem into another class. -/
inductive Evaluative where
  /-- Into classes 5/6. -/
  | augmentative
  /-- Into classes 7/8. -/
  | diminutive
  deriving DecidableEq, Repr, Fintype

/-- A Swahili noun with its morphological class, the pair of classes whose prefixes it
carries, the gender whose agreements it controls, and its animacy. -/
structure Noun extends GenderedNoun Gender where
  /-- The pair of classes whose prefixes the noun carries. -/
  morphClass : Gender
  /-- Whether the noun denotes an animate. -/
  animate : Bool
  /-- Augmentative or diminutive derivation, if any. -/
  evaluative : Option Evaluative := none
  deriving DecidableEq, Repr

/-- *kikapu* 'basket'. -/
def kikapu : Noun :=
  { form := "kikapu", gloss := "basket", morphClass := .genderD, gender := .genderD,
    animate := false }

/-- *kiti* 'stool'. -/
def kiti : Noun :=
  { form := "kiti", gloss := "stool", morphClass := .genderD, gender := .genderD,
    animate := false }

/-- *mti* 'tree'. -/
def mti : Noun :=
  { form := "mti", gloss := "tree", morphClass := .genderB, gender := .genderB,
    animate := false }

/-- *mguu* 'leg'. -/
def mguu : Noun :=
  { form := "mguu", gloss := "leg", morphClass := .genderB, gender := .genderB,
    animate := false }

/-- *nyumba* 'house'. -/
def nyumba : Noun :=
  { form := "nyumba", gloss := "house", morphClass := .genderE, gender := .genderE,
    animate := false }

/-- *mtu* 'person'. -/
def mtu : Noun :=
  { form := "mtu", gloss := "person", morphClass := .genderA, gender := .genderA,
    animate := true }

/-- *mwalimu* 'teacher'. -/
def mwalimu : Noun :=
  { form := "mwalimu", gloss := "teacher", morphClass := .genderA, gender := .genderA,
    animate := true }

/-- *mnyama* 'animal'. -/
def mnyama : Noun :=
  { form := "mnyama", gloss := "animal", morphClass := .genderA, gender := .genderA,
    animate := true }

/-- *mdudu* 'insect'. -/
def mdudu : Noun :=
  { form := "mdudu", gloss := "insect", morphClass := .genderA, gender := .genderA,
    animate := true }

/-- *kifaru* 'rhinoceros', with the prefix of class 7 and the agreements of classes 1/2. -/
def kifaru : Noun :=
  { form := "kifaru", gloss := "rhinoceros", morphClass := .genderD, gender := .genderA,
    animate := true }

/-- *kiboko* 'hippopotamus', with the prefix of class 7 and the agreements of classes 1/2. -/
def kiboko : Noun :=
  { form := "kiboko", gloss := "hippopotamus", morphClass := .genderD, gender := .genderA,
    animate := true }

/-- *mjusi* 'lizard', with the prefix of class 3. -/
def mjusi : Noun :=
  { form := "mjusi", gloss := "lizard", morphClass := .genderB, gender := .genderA,
    animate := true }

/-- *jogoo* 'rooster', of morphological class 5/6. -/
def jogoo : Noun :=
  { form := "jogoo", gloss := "rooster", morphClass := .genderC, gender := .genderA,
    animate := true }

/-- *kipofu* 'blind person', with the prefix of class 7. -/
def kipofu : Noun :=
  { form := "kipofu", gloss := "blind person", morphClass := .genderD, gender := .genderA,
    animate := true }

/-- *tembo* 'elephant', of morphological class 9/10. -/
def tembo : Noun :=
  { form := "tembo", gloss := "elephant", morphClass := .genderE, gender := .genderA,
    animate := true }

/-- *nyoka* 'snake', of morphological class 9/10. -/
def nyoka : Noun :=
  { form := "nyoka", gloss := "snake", morphClass := .genderE, gender := .genderA,
    animate := true }

/-- *rafiki* 'friend', of morphological class 9/10. -/
def rafiki : Noun :=
  { form := "rafiki", gloss := "friend", morphClass := .genderE, gender := .genderA,
    animate := true }

/-- *ng'ombe* 'cow', of morphological class 9/10. -/
def ngombe : Noun :=
  { form := "ng'ombe", gloss := "cow", morphClass := .genderE, gender := .genderA,
    animate := true }

/-- *joka* 'giant snake', the augmentative of *nyoka*. -/
def joka : Noun :=
  { form := "joka", gloss := "giant snake", morphClass := .genderC, gender := .genderC,
    animate := true, evaluative := some .augmentative }

/-- *kitoto* 'baby', the diminutive of *mtoto* 'child'. -/
def kitoto : Noun :=
  { form := "kitoto", gloss := "baby", morphClass := .genderD, gender := .genderD,
    animate := true, evaluative := some .diminutive }

/-- *kijoka* 'tiny snake', the diminutive of *joka*. -/
def kijoka : Noun :=
  { form := "kijoka", gloss := "tiny snake", morphClass := .genderD, gender := .genderD,
    animate := true, evaluative := some .diminutive }

/-- The nouns of Corbett's examples and rules. -/
def allNouns : List Noun :=
  [kikapu, kiti, mti, mguu, nyumba, mtu, mwalimu, mnyama, mdudu, kifaru, kiboko, mjusi, jogoo,
    kipofu, tembo, nyoka, rafiki, ngombe, joka, kitoto, kijoka]

end Swahili
