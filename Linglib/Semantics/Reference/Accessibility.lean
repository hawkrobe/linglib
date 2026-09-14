/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Accessibility marking

This file defines the Accessibility Marking Scale of [ariel-1990], as printed in
[ariel-2001]: the classes of referring expression, from a modified full name to a zero,
ordered by the accessibility of the referent they code, so that a more reduced form codes a
more accessible referent (`AccessibilityLevel`). A form is classified by its head, whether it
is modified, whether it carries lexical content, whether a name is full, its deixis, its
stress and whether it is bound (`AccessibilityLevel.head` and the other features), and the
three criteria the scale is claimed to reflect are read off the features: informativity, the
lexical content a form carries; rigidity, its ability to pick out a referent by form alone;
and attenuation, its phonological reduction.

## Main definitions

* `Reference.AccessibilityLevel` — the scale, as a linear order.
* `AccessibilityLevel.head`, `modified`, `lexical`, `full`, `deixis`, `stressed`, `bound` —
  the features of a form class.
* `AccessibilityLevel.informativity`, `rigidity`, `attenuation` — the criteria, from the
  features.

## Implementation notes

The scale is the paper's ordering of its English form classes, taken as data; the criteria
are not individually monotone along it, and which comparisons each criterion predicts is the
business of `Studies/Ariel2001.lean`. The cognitive statuses of referents, as against the
forms that code them, are `Reference.GivennessStatus`.

## References

* [ariel-1990]
* [ariel-2001]
-/

namespace Reference

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

/-- The deixis of a demonstrative. -/
inductive Deixis where
  | distal
  | proximate
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
def deixis : AccessibilityLevel → Option Deixis
  | .distalDemMod | .distalDemNP | .distalDem => some .distal
  | .proxDemMod | .proxDemNP | .proxDem => some .proximate
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

/-- Informativity: the lexical content a form carries, a lexical head, a modifier and a full
name each adding to it. -/
def informativity (l : AccessibilityLevel) : ℕ :=
  (if l.lexical then 1 else 0) + (if l.modified then 1 else 0) + (if l.full then 1 else 0)

/-- Rigidity: a name picks its referent out by form alone, a lexical description by its
content, and a pronominal form by features only. -/
def rigidity (l : AccessibilityLevel) : ℕ :=
  if l.head = .name then 2 else if l.lexical then 1 else 0

/-- Attenuation: phonological reduction, from a lexical form through bare demonstratives and
stressed, unstressed and cliticized pronouns and verbal agreement to a zero. -/
def attenuation (l : AccessibilityLevel) : ℕ :=
  match l.head with
  | .zero => 5
  | .inflection => 4
  | .pronoun => if l.bound then 3 else if l.stressed then 1 else 2
  | .demonstrative => if l.lexical then 0 else 1
  | .name | .description => 0

end AccessibilityLevel

end Reference
