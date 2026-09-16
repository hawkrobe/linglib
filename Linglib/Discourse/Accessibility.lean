/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Reference.Deixis

/-!
# Accessibility marking

The Accessibility Marking Scale of [ariel-1990], as printed in [ariel-2001]: the classes of
referring expression, from a modified full name to a zero, ordered by the accessibility of the
referent they code, so that a more reduced form codes a more accessible referent
(`AccessibilityLevel`). A form is classified by its head, whether it is modified, whether it
carries lexical content, whether a name is full, its deixis, its stress and whether it is bound
(`AccessibilityLevel.head` and the other features), and the three criteria the scale is claimed
to reflect are read off the features: informativity, the lexical information a form carries;
rigidity, its ability to pick out a referent by form alone; and attenuation, its phonological
size. Each is compared, never counted: a form is more informative than another when it carries
everything the other does, and the rigidity and attenuation scales are the chapter's own.

## Main definitions

* `Discourse.AccessibilityLevel`: the scale, as a linear order.
* `AccessibilityLevel.head`, `modified`, `lexical`, `full`, `deixis`, `stressed`, `bound`: the
  features of a form class.
* `AccessibilityLevel.informativity`, `rigidity`, `attenuation`: the criteria, from the
  features, valued in the information a form carries (`Information`, ordered by inclusion),
  its `Rigidity` and its `Attenuation`.

## Implementation notes

The scale is the paper's ordering of its English form classes, taken as data; the criteria
are not individually monotone along it, and which comparisons each criterion predicts is the
business of `Studies/Ariel2001.lean`. The cognitive statuses of referents, as against the
forms that code them, are `Discourse.GivennessStatus`.

## References

* [ariel-1990]
* [ariel-2001]
-/

namespace Discourse

/-- An accessibility level is a class of referring expression on the Accessibility Marking
Scale of [ariel-1990], from the least to the most accessible referent it codes. -/
inductive AccessibilityLevel where
  /-- A modified full name, *the former governor of Alaska, Sarah Palin*. -/
  | fullNameMod
  /-- A full name, *Sarah Palin*. -/
  | fullName
  /-- A long definite description, *the former governor of Alaska*. -/
  | longDefDescription
  /-- A short definite description, *the governor*. -/
  | shortDefDescription
  /-- A last name, *Palin*. -/
  | lastName
  /-- A first name, *Sarah*. -/
  | firstName
  /-- A modified distal demonstrative phrase, *that tall woman over there*. -/
  | distalDemMod
  /-- A modified proximate demonstrative phrase, *this tall woman*. -/
  | proxDemMod
  /-- A distal demonstrative phrase, *that woman*. -/
  | distalDemNP
  /-- A proximate demonstrative phrase, *this woman*. -/
  | proxDemNP
  /-- A distal demonstrative, *that*. -/
  | distalDem
  /-- A proximate demonstrative, *this*. -/
  | proxDem
  /-- A stressed pronoun with a pointing gesture. -/
  | stressedPronGesture
  /-- A stressed pronoun, *SHE*. -/
  | stressedPron
  /-- An unstressed pronoun, *she*. -/
  | unstressedPron
  /-- A cliticized pronoun, *'er*. -/
  | cliticizedPron
  /-- Person inflection on the verb. -/
  | verbalAgreement
  /-- A zero. -/
  | zero
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace AccessibilityLevel

/-- The rank of a form class, higher for the more accessible referent. -/
def rank : AccessibilityLevel → ℕ
  | .fullNameMod         => 0
  | .fullName            => 1
  | .longDefDescription  => 2
  | .shortDefDescription => 3
  | .lastName            => 4
  | .firstName           => 5
  | .distalDemMod        => 6
  | .proxDemMod          => 7
  | .distalDemNP         => 8
  | .proxDemNP           => 9
  | .distalDem           => 10
  | .proxDem             => 11
  | .stressedPronGesture => 12
  | .stressedPron        => 13
  | .unstressedPron      => 14
  | .cliticizedPron      => 15
  | .verbalAgreement     => 16
  | .zero                => 17

/-- `fullNameMod < ⋯ < zero`: the scale. -/
instance : LinearOrder AccessibilityLevel := LinearOrder.lift' rank (by decide)

/-! ### Features -/

/-- The head of a form class. -/
inductive Head where
  | name
  | description
  | demonstrative
  | pronoun
  | inflection
  | zero
  deriving DecidableEq, Repr, Fintype

/-- The head of a form class. -/
def head : AccessibilityLevel → Head
  | .fullNameMod | .fullName | .lastName | .firstName => .name
  | .longDefDescription | .shortDefDescription => .description
  | .distalDemMod | .proxDemMod | .distalDemNP | .proxDemNP | .distalDem | .proxDem =>
    .demonstrative
  | .stressedPronGesture | .stressedPron | .unstressedPron | .cliticizedPron => .pronoun
  | .verbalAgreement => .inflection
  | .zero => .zero

/-- A form carries a modifier, or is the long form of a description. -/
def modified : AccessibilityLevel → Prop
  | .fullNameMod | .longDefDescription | .distalDemMod | .proxDemMod => True
  | _ => False

/-- A form carries lexical content beyond its head, a noun or a name. -/
def lexical : AccessibilityLevel → Prop
  | .fullNameMod | .fullName | .lastName | .firstName | .longDefDescription
  | .shortDefDescription | .distalDemMod | .proxDemMod | .distalDemNP | .proxDemNP => True
  | _ => False

/-- A form is a full rather than a partial name. -/
def full : AccessibilityLevel → Prop
  | .fullNameMod | .fullName => True
  | _ => False

/-- The deixis of a demonstrative form. -/
def deixis : AccessibilityLevel → Option Reference.Deixis
  | .distalDemMod | .distalDemNP | .distalDem => some .distal
  | .proxDemMod | .proxDemNP | .proxDem => some .proximal
  | _ => none

/-- A form is a stressed pronoun. -/
def stressed : AccessibilityLevel → Prop
  | .stressedPronGesture | .stressedPron => True
  | _ => False

/-- A form is a bound pronominal, cliticized or verbal agreement. -/
def bound : AccessibilityLevel → Prop
  | .cliticizedPron | .verbalAgreement => True
  | _ => False

instance : DecidablePred modified := λ l => by cases l <;> unfold modified <;> infer_instance
instance : DecidablePred lexical := λ l => by cases l <;> unfold lexical <;> infer_instance
instance : DecidablePred full := λ l => by cases l <;> unfold full <;> infer_instance
instance : DecidablePred stressed := λ l => by cases l <;> unfold stressed <;> infer_instance
instance : DecidablePred bound := λ l => by cases l <;> unfold bound <;> infer_instance

/-! ### The criteria -/

/-- A piece of the lexical information a form carries. -/
inductive Information where
  /-- A lexical head, a noun or a name. -/
  | lexical
  /-- A modifier, or the long form of a description. -/
  | modifier
  /-- A full rather than a partial name. -/
  | fullName
  deriving DecidableEq, Repr, Fintype

/-- A form carries a piece of information. -/
def Information.CarriedBy : Information → AccessibilityLevel → Prop
  | .lexical, l => l.lexical
  | .modifier, l => l.modified
  | .fullName, l => l.full

instance (l : AccessibilityLevel) : DecidablePred (Information.CarriedBy · l) := fun i => by
  cases i <;> unfold Information.CarriedBy <;> infer_instance

/-- Informativity: the lexical information a form carries, one form more informative than
another when it carries everything the other does. -/
def informativity (l : AccessibilityLevel) : Finset Information :=
  Finset.univ.filter (Information.CarriedBy · l)

/-- How far a form picks out its referent by its form alone. -/
inductive Rigidity where
  /-- A pronominal form: features only. -/
  | pronominal
  /-- A lexical description: by its content. -/
  | descriptive
  /-- A name. -/
  | rigid
  deriving DecidableEq, Repr, Fintype

/-- `pronominal < descriptive < rigid`. -/
instance : LinearOrder Rigidity :=
  LinearOrder.lift' (fun r : Rigidity => match r with
    | .pronominal => (0 : ℕ) | .descriptive => 1 | .rigid => 2) (by decide)

/-- Rigidity: a name picks its referent out by form alone, a lexical description by its
content, and a pronominal form by features only. -/
def rigidity (l : AccessibilityLevel) : Rigidity :=
  if l.head = .name then .rigid else if l.lexical then .descriptive else .pronominal

/-- The phonological size of a form. -/
inductive Attenuation where
  /-- A lexical phrase: a name, a description or a demonstrative with a noun. -/
  | phrase
  /-- A stressed word: a stressed pronoun or a bare demonstrative. -/
  | stressedWord
  /-- An unstressed word. -/
  | unstressedWord
  /-- A clitic. -/
  | clitic
  /-- Verbal inflection. -/
  | inflection
  /-- Nothing. -/
  | zero
  deriving DecidableEq, Repr, Fintype

/-- `phrase < stressedWord < unstressedWord < clitic < inflection < zero`: the more attenuated
the form, the higher. -/
instance : LinearOrder Attenuation :=
  LinearOrder.lift' (fun a : Attenuation => match a with
    | .phrase => (0 : ℕ) | .stressedWord => 1 | .unstressedWord => 2 | .clitic => 3
    | .inflection => 4 | .zero => 5) (by decide)

/-- Attenuation: the phonological reduction of a form, from a lexical phrase through bare
demonstratives and stressed, unstressed and cliticized pronouns and verbal agreement to a
zero. -/
def attenuation (l : AccessibilityLevel) : Attenuation :=
  match l.head with
  | .zero => .zero
  | .inflection => .inflection
  | .pronoun => if l.bound then .clitic else if l.stressed then .stressedWord else .unstressedWord
  | .demonstrative => if l.lexical then .phrase else .stressedWord
  | .name | .description => .phrase

end AccessibilityLevel

end Discourse
