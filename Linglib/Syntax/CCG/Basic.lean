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
only in the slash directions the schema passes through (the Principle of Inheritance). `Derivation` is intrinsically
typed — its constructors are the rule instances the toy grammar admits, so a value of
`Derivation α c` *is* a derivation of category `c` and "derives `S`" is typechecking.
The target-restricted (VW-CCG) schema derivations live in `CCG.TargetRestricted`.

## Main definitions

* `Cat`: categories over an atom type `α` — atoms plus directional slashes.
* `Cat.generalizedForwardComp`, `Cat.generalizedBackwardComp`: generalized
  composition of degree `n`, the schema every binary rule instantiates.
* `Cat.forwardTypeRaise`, `Cat.backwardTypeRaise`: type-raising.
* `Derivation`: intrinsically typed derivations, indexed by the category they derive;
  `Derivation.yield` reads off the surface string a derivation spells out,
  `Derivation.opCount` the number of rule applications, and `analyzeDerivation` the
  strongest rule class used (`DerivationType`).

## Notation

* `X / Y`: the rightward-looking category `Cat.rslash X Y`.
* `X \ Y`: the leftward-looking category `Cat.lslash X Y`.

Both are scoped to the `CCG` namespace. Because `/` overloads Lean's division,
categories are written fully parenthesized (`(S \ NP) / NP`) rather than relying on
the Steedman left-to-right reading.
-/

namespace CCG

/-! ### Categories -/

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

variable {α : Type*} [DecidableEq α]

namespace Cat

/-! ### The generalized composition schema -/

/-- `generalizedForwardComp n f g` is forward composition of degree `n` (`>Bⁿ`): when
`f = X/Y` and `g = Y|Z₁…|Zₙ`, the result is `X|Z₁…|Zₙ` with each argument keeping its
own slash direction, and `none` otherwise. -/
def generalizedForwardComp : Nat → Cat α → Cat α → Option (Cat α)
  | 0, .rslash x y, z => if y = z then some x else none
  | n + 1, f, .rslash g z => (generalizedForwardComp n f g).map (Cat.rslash · z)
  | n + 1, f, .lslash g z => (generalizedForwardComp n f g).map (Cat.lslash · z)
  | _, _, _ => none

/-- `generalizedBackwardComp n g f` is backward composition of degree `n` (`<Bⁿ`), the
mirror of `generalizedForwardComp`: when `g = Y|Z₁…|Zₙ` and `f = X\Y`, the result is
`X|Z₁…|Zₙ`, and `none` otherwise. -/
def generalizedBackwardComp : Nat → Cat α → Cat α → Option (Cat α)
  | 0, z, .lslash x y => if y = z then some x else none
  | n + 1, .rslash g z, f => (generalizedBackwardComp n g f).map (Cat.rslash · z)
  | n + 1, .lslash g z, f => (generalizedBackwardComp n g f).map (Cat.lslash · z)
  | _, _, _ => none

/-! ### Type-raising -/

/-- `forwardTypeRaise x t` is `t / (t \ x)` — forward type-raising `>T` of `x` to
target `t`. -/
def forwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t / (t \ x)

/-- `backwardTypeRaise x t` is `t \ (t / x)` — backward type-raising `<T` of `x` to
target `t`. -/
def backwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t \ (t / x)

end Cat

/-! ### Derivations -/

/-- A CCG derivation of category `c`, intrinsically typed: each constructor is one of
the toy grammar's rule instances, so a value of `Derivation α c` *is* a well-formed
derivation and "derives `c`" is typechecking. Backward crossed composition and the
substitution rules of [steedman-2000] are not part of this inventory. -/
inductive Derivation (α : Type*) : Cat α → Type _ where
  /-- A lexical leaf: a surface form, at category `c`. -/
  | lex (form : String) (c : Cat α) : Derivation α c
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
  | .lex f _ => [f]
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
  | .lex _ _ => 0
  | .fapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .bapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .fcomp d1 d2 => 1 + d1.opCount + d2.opCount
  | .bcomp d1 d2 => 1 + d1.opCount + d2.opCount
  | .fcompx d1 d2 => 1 + d1.opCount + d2.opCount
  | .ftr d _ => 1 + d.opCount
  | .btr d _ => 1 + d.opCount
  | .coord _ d1 d2 => 1 + d1.opCount + d2.opCount

/-- The rule classes a derivation can be built from, for structural analysis:
pure application, or the scope-relevant devices composition and type-raising. -/
inductive DerivationType where
  /-- Pure application. -/
  | directApp
  /-- At least one type-raising node. -/
  | typeRaised
  /-- At least one composition node (and no type-raising). -/
  | composed
  deriving DecidableEq, Repr

/-- Combine daughters' derivation types — the maximum under
`directApp < composed < typeRaised`. -/
def DerivationType.join : DerivationType → DerivationType → DerivationType
  | .typeRaised, _ | _, .typeRaised => .typeRaised
  | .composed, _ | _, .composed => .composed
  | _, _ => .directApp

/-- The derivation type of a derivation: composition and type-raising nodes dominate
their subtrees. -/
def analyzeDerivation {c : Cat α} : Derivation α c → DerivationType
  | .lex _ _ => .directApp
  | .fapp d1 d2 => (analyzeDerivation d1).join (analyzeDerivation d2)
  | .bapp d1 d2 => (analyzeDerivation d1).join (analyzeDerivation d2)
  | .fcomp _ _ => .composed
  | .bcomp _ _ => .composed
  | .fcompx _ _ => .composed
  | .ftr _ _ => .typeRaised
  | .btr _ _ => .typeRaised
  | .coord _ d1 d2 => (analyzeDerivation d1).join (analyzeDerivation d2)

end CCG
