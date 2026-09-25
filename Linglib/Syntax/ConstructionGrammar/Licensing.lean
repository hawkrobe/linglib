/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Basic
public import Linglib.Syntax.Tree.Basic

/-!
# Constructional licensing

A constructional grammar licenses a structure when every constituent in it instantiates some
construction ([sag-2012]; [goldberg-1995]). `Licenses` is the local version of that relation
over constituency trees: every internal node's daughters instantiate, slot by slot, the typed
form of some construction of an inventory (`FormMatches`), and words are licensed lexically.
A node is licensed by the form of one construction alone, without the constraints it inherits
from the constructions above it in a network.

Matching is relative to a `Lexicon`, the part of speech of each word and the words that negate.
A `headed` filler is checked against the immediate daughters, a flat approximation of
headedness, and a `semantic` filler, which the form cannot check, matches anything. Of the
slot constraints only `negMinus` bears on the daughter itself: it rejects a negated daughter
(`SlotConstraint.Allows`).

## Main declarations

- `Lexicon`: parts of speech and negators
- `SlotFiller.Matches`, `SlotConstraint.Allows`, `Slot.Admits`, `FormMatches`: matching daughters
  against a form
- `LicensedLocally`, `Licenses`: the licensing relation

## References

* [sag-2012]
* [goldberg-1995]
* [kay-fillmore-1999]
-/

@[expose] public section

namespace ConstructionGrammar

open Syntax (Tree)

/-- What the recognizer knows of words: the part of speech of each, and the words that negate,
which a `negMinus` slot rejects. -/
structure Lexicon where
  /-- The part of speech of each word. -/
  pos : String → Option UD.UPOS
  /-- The negators. -/
  negators : List String := []

variable (lex : Lexicon)

/-- A daughter fills a slot: a fixed word is that word, an open slot a word of its part of
speech, a phrasal slot any constituent, and a headed slot a constituent with its head word, of
its part of speech, among the daughters. -/
def SlotFiller.Matches : SlotFiller String → Tree Unit String → Prop
  | .fixed w, .terminal _ w' => w = w'
  | .open_ c, .terminal _ w => lex.pos w = some c
  | .phrasal, .node _ _ => True
  | .headed h c, .node _ ts => .terminal () h ∈ ts ∧ lex.pos h = some c
  | .semantic _, _ => True
  | _, _ => False

instance : ∀ (f : SlotFiller String) (t : Tree Unit String), Decidable (f.Matches lex t)
  | .fixed w, .terminal _ w' => inferInstanceAs (Decidable (w = w'))
  | .open_ c, .terminal _ w => inferInstanceAs (Decidable (lex.pos w = some c))
  | .phrasal, .node _ _ => isTrue trivial
  | .headed h c, .node _ ts =>
      inferInstanceAs (Decidable (.terminal () h ∈ ts ∧ lex.pos h = some c))
  | .semantic _, _ => isTrue trivial
  | .fixed _, .node _ _ | .fixed _, .trace _ _ | .fixed _, .bind _ _ _
  | .open_ _, .node _ _ | .open_ _, .trace _ _ | .open_ _, .bind _ _ _
  | .phrasal, .terminal _ _ | .phrasal, .trace _ _ | .phrasal, .bind _ _ _
  | .headed _ _, .terminal _ _ | .headed _ _, .trace _ _ | .headed _ _, .bind _ _ _ => isFalse id

/-- A daughter respects a slot constraint. `negMinus` forbids a negator, as the daughter or among
its daughters; `locMinus` and `refEmpty` concern the slot's external syntax and semantics and
are not checkable against the daughter itself. -/
def SlotConstraint.Allows : SlotConstraint → Tree Unit String → Prop
  | .negMinus, .terminal _ w => w ∉ lex.negators
  | .negMinus, .node _ ts => ∀ w ∈ lex.negators, .terminal () w ∉ ts
  | _, _ => True

instance : ∀ (c : SlotConstraint) (t : Tree Unit String), Decidable (c.Allows lex t)
  | .negMinus, .terminal _ w => inferInstanceAs (Decidable (w ∉ lex.negators))
  | .negMinus, .node _ ts => inferInstanceAs (Decidable (∀ w ∈ lex.negators, .terminal () w ∉ ts))
  | .negMinus, .trace _ _ | .negMinus, .bind _ _ _ | .locMinus, _ | .refEmpty, _ => isTrue trivial

/-- A daughter instantiates a slot: it fills the slot and respects its constraints. -/
def Slot.Admits (s : Slot String) (t : Tree Unit String) : Prop :=
  s.filler.Matches lex t ∧ ∀ c ∈ s.constraints, c.Allows lex t

instance (s : Slot String) (t : Tree Unit String) : Decidable (s.Admits lex t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A daughter sequence instantiates a typed form, slot by slot. -/
def FormMatches (form : TypedForm String) (ts : List (Tree Unit String)) : Prop :=
  List.Forall₂ (Slot.Admits lex) form ts

instance (form : TypedForm String) (ts : List (Tree Unit String)) :
    Decidable (FormMatches lex form ts) :=
  inferInstanceAs (Decidable (List.Forall₂ _ form ts))

variable {Sem : Type*} (cxns : List (Construction Sem))

/-- A node is licensed locally when a word, or when its daughters instantiate the form of some
construction of the inventory; traces and binders are not. -/
def LicensedLocally : Tree Unit String → Prop
  | .terminal _ _ => True
  | .node _ ts => ∃ c ∈ cxns, FormMatches lex c.form ts
  | .trace _ _ | .bind _ _ _ => False

instance : ∀ t : Tree Unit String, Decidable (LicensedLocally lex cxns t)
  | .terminal _ _ => isTrue trivial
  | .node _ ts => inferInstanceAs (Decidable (∃ c ∈ cxns, FormMatches lex c.form ts))
  | .trace _ _ | .bind _ _ _ => isFalse id

/-- The inventory licenses a tree when every constituent in it is licensed locally. -/
def Licenses (t : Tree Unit String) : Prop := ∀ s ∈ t.subtrees, LicensedLocally lex cxns s

instance (t : Tree Unit String) : Decidable (Licenses lex cxns t) :=
  inferInstanceAs (Decidable (∀ s ∈ t.subtrees, _))

end ConstructionGrammar
