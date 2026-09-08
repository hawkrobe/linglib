import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Classifier.Basic

/-!
# Swahili noun classes

This file defines the Swahili noun-class system: the fifteen classes with their subject
markers, the five genders that pair a singular class with its plural ([carstens-1991],
[scott-2021]), and the parameters of the class system as a classifier device. Class conditions
subject and object agreement, possessive and demonstrative agreement and, in relativization,
the form of the resumptive pronoun.

## References

* [carstens-1991]
* [scott-2021]
-/

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

end Swahili
