module

public import Linglib.Fragments.Bantu.Params

/-!
# Shona noun classes

This file defines the Shona noun-class system: the fourteen classes with their subject markers,
the eight genders that pair a singular class with its plural, two of them sharing a plural
class, and the semantic core each gender bears ([carstens-2026]).

## References

* [carstens-2026]
-/

@[expose] public section

namespace Shona

open Bantu

/-! ### Classes -/

/-- The noun classes in the Bantu numbering; classes 15–18 are absent or unproductive. -/
inductive NounClass where
  /-- *mu-*: murume 'man'. -/
  | cl1
  /-- *va-*: varume 'men'. -/
  | cl2
  /-- *mu-*: muti 'tree'. -/
  | cl3
  /-- *mi-*: miti 'trees'. -/
  | cl4
  /-- *ri-*, often unprefixed: zai 'egg'. -/
  | cl5
  /-- *ma-*: mazai 'eggs'. -/
  | cl6
  /-- *chi-*: chingwa 'bread'. -/
  | cl7
  /-- *zvi-*: zvingwa 'loaves'. -/
  | cl8
  /-- *n-*: imbwa 'dog'. -/
  | cl9
  /-- *n-*, *dzi-*: imbwa 'dogs'. -/
  | cl10
  /-- *ru-*: rukova 'stream'. -/
  | cl11
  /-- *ka-*, the diminutive singular: kasikana 'small girl'. -/
  | cl12
  /-- *tu-*, the diminutive plural: tusikana 'small girls'. -/
  | cl13
  /-- *hu-*, *u-*: huchi 'honey'. -/
  | cl14
  deriving DecidableEq, Repr

/-- The subject marker of a class on the verb. -/
def NounClass.subjPrefix : NounClass → String
  | .cl1 => "a"
  | .cl2 => "va"
  | .cl3 => "u"
  | .cl4 => "i"
  | .cl5 => "ri"
  | .cl6 => "a"
  | .cl7 => "chi"
  | .cl8 => "zvi"
  | .cl9 => "i"
  | .cl10 => "dzi"
  | .cl11 => "ru"
  | .cl12 => "ka"
  | .cl13 => "tu"
  | .cl14 => "hu"

/-! ### Genders -/

/-- The eight genders, each pairing a singular class with its plural; the plurals of classes 11
and 14 are those of classes 9 and 5. -/
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
  /-- Classes 11/10. -/
  | genderF
  /-- Classes 14/6. -/
  | genderG
  /-- Classes 12/13, the diminutives. -/
  | genderH
  deriving DecidableEq, Repr

def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9
  | .genderF => .cl11
  | .genderG => .cl14
  | .genderH => .cl12

def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10
  | .genderF => .cl10
  | .genderG => .cl6
  | .genderH => .cl13

/-- The gender whose singular class a class is, none for a plural class. -/
def Gender.ofSingular : NounClass → Option Gender
  | .cl1 => some .genderA
  | .cl3 => some .genderB
  | .cl5 => some .genderC
  | .cl7 => some .genderD
  | .cl9 => some .genderE
  | .cl11 => some .genderF
  | .cl14 => some .genderG
  | .cl12 => some .genderH
  | _ => none

@[simp] theorem Gender.ofSingular_singularClass (g : Gender) :
    ofSingular g.singularClass = some g := by
  cases g <;> rfl

/-- The semantic core of each gender: A bears [human] and D [non-human], the core and default of
everything else; the other six bear none. -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderD => .interpretable .nonhuman
  | _ => .uninterpretable

end Shona
