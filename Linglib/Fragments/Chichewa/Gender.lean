import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Gender.Basic

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

/-- A plural noun with its gender and whether it denotes humans. -/
structure Noun where
  /-- The plural form, with its class prefix. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The agreement the noun takes. -/
  attestedGender : Value
  /-- Whether the noun denotes humans. -/
  human : Bool
  deriving DecidableEq, Repr

/-- The gender the noun controls. -/
abbrev Noun.gender (n : Noun) : Value := n.attestedGender

/-- *a-mphaka* 'cats': gender 1/2 without denoting humans. -/
def mphaka : Noun := ⟨"a-mphaka", "cats", .g1_2, false⟩
/-- *a-galu* 'dogs'. -/
def galu : Noun := ⟨"a-galu", "dogs", .g1_2, false⟩
/-- *a-na* 'children'. -/
def ana : Noun := ⟨"a-na", "children", .g1_2, true⟩
/-- *ma-lalanje* 'oranges'. -/
def lalanje : Noun := ⟨"ma-lalanje", "oranges", .g5_6, false⟩
/-- *ma-samba* 'leaves'. -/
def samba : Noun := ⟨"ma-samba", "leaves", .g5_6, false⟩
/-- *zipewa* 'hats'. -/
def zipewa : Noun := ⟨"zipewa", "hats", .g7_8, false⟩

/-- The nouns the sources cite. -/
def allNouns : List Noun := [mphaka, galu, ana, lalanje, samba, zipewa]

end Chichewa.Gender
