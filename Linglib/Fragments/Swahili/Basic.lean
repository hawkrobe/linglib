module

public import Mathlib.Tactic.DeriveFintype

/-!
# Swahili noun classes

This file defines the Swahili noun-class system: the fifteen classes with their subject
markers and the five genders that pair a singular class with its plural ([carstens-1991],
[scott-2021]). Class conditions
subject and object agreement, possessive and demonstrative agreement and, in relativization,
the form of the resumptive pronoun.

## References

* [carstens-1991]
* [scott-2021]
-/

@[expose] public section

namespace Swahili

/-! ### Classes -/

/-- The noun classes in the Bantu numbering; classes 11–13 are absent. -/
inductive NounClass where
  /-- *m-*, *mw-*: mtoto 'child'. -/
  | cl1
  /-- *wa-*: watoto 'children'. -/
  | cl2
  /-- *m-*, *mw-*: mti 'tree'. -/
  | cl3
  /-- *mi-*: miti 'trees'. -/
  | cl4
  /-- *ji-*, often unprefixed: jicho 'eye'. -/
  | cl5
  /-- *ma-*: macho 'eyes'. -/
  | cl6
  /-- *ki-*: kiti 'chair'. -/
  | cl7
  /-- *vi-*: viti 'chairs'. -/
  | cl8
  /-- *n-*, often unprefixed: nyumba 'house'. -/
  | cl9
  /-- *n-*, often unprefixed: nyumba 'houses'. -/
  | cl10
  /-- *u-*, the abstract class: uzuri 'beauty'. -/
  | cl14
  /-- *ku-*, the infinitive class: kusoma 'to read'. -/
  | cl15
  /-- *pa-*, definite location: mahali 'place'. -/
  | cl16
  /-- *ku-*, indefinite location. -/
  | cl17
  /-- *mu-*, *m-*, interior location. -/
  | cl18
  deriving DecidableEq, Repr, Fintype

/-- The subject marker of a class on the verb. -/
def NounClass.subjPrefix : NounClass → String
  | .cl1 => "a"
  | .cl2 => "wa"
  | .cl3 => "u"
  | .cl4 => "i"
  | .cl5 => "li"
  | .cl6 => "ya"
  | .cl7 => "ki"
  | .cl8 => "vi"
  | .cl9 => "i"
  | .cl10 => "zi"
  | .cl14 => "u"
  | .cl15 => "ku"
  | .cl16 => "pa"
  | .cl17 => "ku"
  | .cl18 => "mu"

/-! ### Genders -/

/-- The five genders, each pairing a singular class with its plural. -/
inductive Gender where
  /-- Classes 1/2. -/
  | genderA
  /-- Classes 3/4. -/
  | genderB
  /-- Classes 5/6. -/
  | genderC
  /-- Classes 7/8. -/
  | genderD
  /-- Classes 9/10. -/
  | genderE
  deriving DecidableEq, Repr, Fintype

def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9

def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10

end Swahili
