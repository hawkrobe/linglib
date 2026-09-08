import Mathlib.Tactic.DeriveFintype
import Linglib.Fragments.Bantu.Params
import Linglib.Syntax.Category.Classifier.Basic

/-!
# Xhosa noun classes

This file defines the Xhosa noun-class system: the eleven classes with their subject markers,
the five genders that pair a singular class with its plural ([carstens-1991]), the semantic core
each gender bears ([carstens-2026]), and the parameters of the class system as a classifier
device.

## References

* [carstens-1991]
* [carstens-2026]
* [taraldsen-et-al-2018]
-/

namespace Xhosa

open Bantu

/-! ### Classes -/

/-- The noun classes in the Bantu numbering; classes 11–14 and 16–18 are absent. -/
inductive NounClass where
  /-- *um-*, *u-*: umntu 'person'. -/
  | cl1
  /-- *aba-*: abantu 'people'. -/
  | cl2
  /-- *um-*: umthi 'tree'. -/
  | cl3
  /-- *imi-*: imithi 'trees'. -/
  | cl4
  /-- *i-*: iqanda 'egg'. -/
  | cl5
  /-- *ama-*: amaqanda 'eggs'. -/
  | cl6
  /-- *isi-*: isitya 'dish'. -/
  | cl7
  /-- *izi-*: izitya 'dishes'. -/
  | cl8
  /-- *in-*: inja 'dog'. -/
  | cl9
  /-- *iin-*: iinja 'dogs'. -/
  | cl10
  /-- *uku-*, the infinitive and gerund class: ukucula 'to sing'. -/
  | cl15
  deriving DecidableEq, Repr, Fintype

/-- The subject marker of a class on the verb. -/
def NounClass.subjPrefix : NounClass → String
  | .cl1 => "u"
  | .cl2 => "ba"
  | .cl3 => "u"
  | .cl4 => "i"
  | .cl5 => "li"
  | .cl6 => "a"
  | .cl7 => "si"
  | .cl8 => "zi"
  | .cl9 => "i"
  | .cl10 => "zi"
  | .cl15 => "ku"

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

/-- The gender whose singular class a class is, none for a plural class or class 15. -/
def Gender.ofSingular : NounClass → Option Gender
  | .cl1 => some .genderA
  | .cl3 => some .genderB
  | .cl5 => some .genderC
  | .cl7 => some .genderD
  | .cl9 => some .genderE
  | _ => none

@[simp] theorem Gender.ofSingular_singularClass (g : Gender) :
    ofSingular g.singularClass = some g := by
  cases g <;> rfl

/-- The subject marker of a gender's plural class. -/
def Gender.plSubjPrefix (g : Gender) : String := g.pluralClass.subjPrefix

/-- The semantic core of each gender: A bears [human], D [inanimate] and E [animal], while B
and C bear none. -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderB => .uninterpretable
  | .genderC => .uninterpretable
  | .genderD => .interpretable .inanimate
  | .genderE => .interpretable .animal

/-! ### Noun-class parameters -/

/-- Gender is realized by agreement inside the head-modifier NP; the clause is a further scope. -/
def classifierLocus : Classifier.Scope := .headModifierNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.headModifierNP, .predicateArgument]

/-- Semantic core with morphological residue. -/
def classifierAssignment : Classifier.Assignment := .mixed

/-- Class prefixes on the noun and its agreement targets. -/
def classifierRealizations : List Classifier.Realization := [.prefix]

def classifierAgreement : Bool := true

def classifierObligatory : Bool := true

/-- A default agreement class. -/
def classifierDefault : Bool := true

def classifierSemantics : List Classifier.Parameter := [.humanness, .animacy]

def obligatoryNumber : Bool := true

end Xhosa
