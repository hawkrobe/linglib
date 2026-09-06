import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Noun.Basic

/-!
# Chichewa noun gender

Chichewa genders are pairs of Bantu noun classes, one for each number, and are named by
them. Subject agreement does not distinguish them all: the plural of gender 1/2, the human
gender, and the plural of gender 5/6 both take the verbal prefix *a-*, while the plural of
gender 7/8 takes *zi-* ([corbett-mtenje-1987]; [corbett-1991]; [corbett-1998]). The
entries are the plural nouns the sources cite.

## TODO

* The remaining genders and their prefixes, and number on the nouns, from
  [corbett-mtenje-1987].

## References

* [G. G. Corbett, A. D. Mtenje, *Gender agreement in Chichewa* (1987)][corbett-mtenje-1987]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
-/

namespace Chichewa.Gender

/-- The genders the sources attest, by singular and plural class. -/
inductive Value where
  | g1_2
  | g5_6
  | g7_8
  deriving DecidableEq, Repr, Fintype

/-- The subject prefixes plural controllers take. -/
inductive SubjPrefix where
  | a
  | zi
  deriving DecidableEq, Repr, Fintype

/-- The subject prefix of each gender's plural. -/
def Value.plSubjPrefix : Value → SubjPrefix
  | .g1_2 | .g5_6 => .a
  | .g7_8 => .zi

/-- A plural noun, its form carrying its class prefix, with its gender and whether it
denotes humans. -/
structure Noun extends GenderedNoun Value where
  /-- Whether the noun denotes humans. -/
  human : Bool
  deriving DecidableEq, Repr

/-- *a-mphaka* 'cats': gender 1/2 without denoting humans. -/
def mphaka : Noun := { form := "a-mphaka", gloss := "cats", gender := .g1_2, human := false }
/-- *a-galu* 'dogs'. -/
def galu : Noun := { form := "a-galu", gloss := "dogs", gender := .g1_2, human := false }
/-- *a-na* 'children'. -/
def ana : Noun := { form := "a-na", gloss := "children", gender := .g1_2, human := true }
/-- *ma-lalanje* 'oranges'. -/
def lalanje : Noun := { form := "ma-lalanje", gloss := "oranges", gender := .g5_6, human := false }
/-- *ma-samba* 'leaves'. -/
def samba : Noun := { form := "ma-samba", gloss := "leaves", gender := .g5_6, human := false }
/-- *zipewa* 'hats'. -/
def zipewa : Noun := { form := "zipewa", gloss := "hats", gender := .g7_8, human := false }

/-- The nouns the sources cite. -/
def allNouns : List Noun := [mphaka, galu, ana, lalanje, samba, zipewa]

end Chichewa.Gender
