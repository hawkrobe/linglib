import Linglib.Syntax.Category.Coordinator

/-!
# Combinatory Categorial Grammar (CCG)

This file defines Combinatory Categorial Grammar (CCG): categories that encode
argument structure through directional slashes, the combinatory rule schema that
combines them, and intrinsically typed derivations ([steedman-2000]).

Categories are stated over an arbitrary type `α` of atomic categories, so a grammar
needing featured atoms (e.g. [steedman-2000]'s `S₊SUB` and `VP₋SUB` for Dutch) can
instantiate a richer inventory than the featureless core `CCG.Atom`.

Every binary rule is an instance of one schema, generalized composition of degree `n`:
degree 0 is application, and at degree ≥ 1 the harmonic and crossed variants differ
only in the slash directions the schema passes through. `Derivation` is intrinsically
typed — its constructors are the rule instances the toy grammar admits, so a value of
`Derivation α c` *is* a derivation of category `c` and "derives `S`" is typechecking.
The target-restricted (VW-CCG) schema derivations live in `CCG.TargetRestricted`.

## Main definitions

* `Cat`: categories over an atom type `α` — atoms plus directional slashes.
* `Cat.generalizedForwardComp`, `Cat.generalizedBackwardComp`: generalized
  composition of degree `n`, the schema every binary rule instantiates.
* `Cat.forwardTypeRaise`, `Cat.backwardTypeRaise`: type-raising.
* `LexEntry`: a lexical entry, pairing a surface form with its category.
* `Derivation`: intrinsically typed derivations, indexed by the category they derive;
  `Derivation.yield` reads off the surface string a derivation spells out and
  `Derivation.opCount` the number of rule applications.

## Notation

* `X / Y`: the rightward-looking category `Cat.rslash X Y`.
* `X \ Y`: the leftward-looking category `Cat.lslash X Y`.

Both are scoped to the `CCG` namespace. Because `/` overloads Lean's division,
categories are written fully parenthesized (`(S \ NP) / NP`) rather than relying on
the Steedman left-to-right reading.
-/

namespace CCG

section Categories

/-- The core atomic categories of the English fragment (`S`, `NP`, `N`, `PP`, as in
[steedman-2000]), stated without features. -/
inductive Atom where
  /-- Sentence. -/
  | S
  /-- Noun phrase. -/
  | NP
  /-- Common noun. -/
  | N
  /-- Prepositional phrase. -/
  | PP
  deriving Repr, DecidableEq

/-- CCG categories over a type `α` of atomic categories. -/
inductive Cat (α : Type*) where
  /-- An atomic category. -/
  | atom : α → Cat α
  /-- `X/Y`: looking right for a `Y` to give an `X`. -/
  | rslash : Cat α → Cat α → Cat α
  /-- `X\Y`: looking left for a `Y` to give an `X`. -/
  | lslash : Cat α → Cat α → Cat α
  deriving Repr, DecidableEq

scoped notation:60 X "/" Y => Cat.rslash X Y
scoped notation:60 X "\\" Y => Cat.lslash X Y

def S : Cat Atom := .atom .S
def NP : Cat Atom := .atom .NP
def N : Cat Atom := .atom .N
def PP : Cat Atom := .atom .PP

def IV : Cat Atom := S \ NP
def TV : Cat Atom := (S \ NP) / NP
def Det : Cat Atom := NP / N

end Categories

variable {α : Type*} [DecidableEq α]

namespace Cat

section CombinatoryRules

/-- Generalized forward composition `>Bⁿ`, the rule schema of
[vijay-shanker-weir-1994] and [steedman-2000]: `X/Y Y|Z₁…|Zₙ ⇒ X|Z₁…|Zₙ`, peeling
the secondary input's last `n` arguments — each keeping its own slash direction, the
Principle of Inheritance — and matching the remainder against `Y`. Degree 0 is forward
application; at degree ≥ 1 the harmonic and crossed instances fall out of the slash
directions rather than being separate rule classes. -/
def generalizedForwardComp : Nat → Cat α → Cat α → Option (Cat α)
  | 0, .rslash x y, z => if y = z then some x else none
  | n + 1, f, .rslash g z => (generalizedForwardComp n f g).map (Cat.rslash · z)
  | n + 1, f, .lslash g z => (generalizedForwardComp n f g).map (Cat.lslash · z)
  | _, _, _ => none

/-- Generalized backward composition `<Bⁿ`: `Y|Z₁…|Zₙ X\Y ⇒ X|Z₁…|Zₙ`, the mirror of
`generalizedForwardComp`. Degree 0 is backward application. -/
def generalizedBackwardComp : Nat → Cat α → Cat α → Option (Cat α)
  | 0, z, .lslash x y => if y = z then some x else none
  | n + 1, .rslash g z, f => (generalizedBackwardComp n g f).map (Cat.rslash · z)
  | n + 1, .lslash g z, f => (generalizedBackwardComp n g f).map (Cat.lslash · z)
  | _, _, _ => none

end CombinatoryRules

section TypeRaising

/-- Forward type-raising: X => T/(T\X). -/
def forwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t / (t \ x)

/-- Backward type-raising: X => T\(T/X). -/
def backwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t \ (t / x)

end TypeRaising

end Cat

/-- A CCG lexical entry. -/
structure LexEntry (α : Type*) where
  form : String
  cat : Cat α
  deriving Repr

section Derivations

/-- A CCG derivation of category `c`, intrinsically typed: each constructor is one of
the toy grammar's rule instances, so a value of `Derivation α c` *is* a well-formed
derivation and "derives `c`" is typechecking. Backward crossed composition and the
substitution rules of [steedman-2000] are not part of this inventory. -/
inductive Derivation (α : Type*) : Cat α → Type _ where
  /-- A lexical leaf, at its entry's category. -/
  | lex (e : LexEntry α) : Derivation α e.cat
  /-- Forward application `>`: X/Y Y ⇒ X. -/
  | fapp {x y : Cat α} : Derivation α (x / y) → Derivation α y → Derivation α x
  /-- Backward application `<`: Y X\Y ⇒ X. -/
  | bapp {x y : Cat α} : Derivation α y → Derivation α (x \ y) → Derivation α x
  /-- Forward harmonic composition `>B`: X/Y Y/Z ⇒ X/Z. -/
  | fcomp {x y z : Cat α} :
      Derivation α (x / y) → Derivation α (y / z) → Derivation α (x / z)
  /-- Backward harmonic composition `<B`: Y\Z X\Y ⇒ X\Z. -/
  | bcomp {x y z : Cat α} :
      Derivation α (y \ z) → Derivation α (x \ y) → Derivation α (x \ z)
  /-- Forward crossed composition `>B×`: X/Y Y\Z ⇒ X\Z. -/
  | fcompx {x y z : Cat α} :
      Derivation α (x / y) → Derivation α (y \ z) → Derivation α (x \ z)
  /-- Forward type-raising to target `t`: X ⇒ T/(T\X). -/
  | ftr {x : Cat α} : Derivation α x → (t : Cat α) → Derivation α (t / (t \ x))
  /-- Backward type-raising to target `t`: X ⇒ T\(T/X). -/
  | btr {x : Cat α} : Derivation α x → (t : Cat α) → Derivation α (t \ (t / x))
  /-- Coordination (X c X ⇒ X); identity of the conjunct categories is enforced by the
      index. Carries the coordinator itself: its `role` fixes the semantic operation
      (`Derivation.interp`) and its `form` is spelled out in the yield. -/
  | coord {x : Cat α} : Coordinator → Derivation α x → Derivation α x → Derivation α x

/-- The surface string a derivation spells out: its leaf forms and coordinators, left
to right.

Combinatory rules concatenate their daughters and type-raising leaves the string
untouched, so the yield is independent of the derivation's combinatory structure —
the property that lets a CCG derivation witness a string language. -/
def Derivation.yield {c : Cat α} : Derivation α c → List String
  | .lex e => [e.form]
  | .fapp d1 d2 => d1.yield ++ d2.yield
  | .bapp d1 d2 => d1.yield ++ d2.yield
  | .fcomp d1 d2 => d1.yield ++ d2.yield
  | .bcomp d1 d2 => d1.yield ++ d2.yield
  | .fcompx d1 d2 => d1.yield ++ d2.yield
  | .ftr d _ => d.yield
  | .btr d _ => d.yield
  | .coord co d1 d2 => d1.yield ++ co.form :: d2.yield

/-- The number of combinatory rule applications in a derivation. -/
def Derivation.opCount {c : Cat α} : Derivation α c → Nat
  | .lex _ => 0
  | .fapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .bapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .fcomp d1 d2 => 1 + d1.opCount + d2.opCount
  | .bcomp d1 d2 => 1 + d1.opCount + d2.opCount
  | .fcompx d1 d2 => 1 + d1.opCount + d2.opCount
  | .ftr d _ => 1 + d.opCount
  | .btr d _ => 1 + d.opCount
  | .coord _ d1 d2 => 1 + d1.opCount + d2.opCount

end Derivations

section Examples

-- "John sees Mary": forward then backward application — deriving `S` is typechecking.
example : Derivation Atom S :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

-- Type-raising a subject: NP ⇒ S/(S\NP).
example : Derivation Atom (S / (S \ NP)) := .ftr (.lex ⟨"John", NP⟩) S

-- The yield spells out the surface string, coordinator included.
example :
    (Derivation.coord { form := "and", gloss := "and", role := .j, kind := .free }
      (.bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩))
      (.bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"laughs", IV⟩))).yield
      = ["John", "sleeps", "and", "Mary", "laughs"] := rfl

end Examples

end CCG
