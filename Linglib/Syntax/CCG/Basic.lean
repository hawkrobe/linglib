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
  `Derivation.trace` the rule applications at its nodes in the schema's vocabulary —
  with `opCount` (length) and `HasComp` / `HasTypeRaise` (membership) read off it.

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

/-- A rule application, in the schema's own vocabulary: generalized composition is
identified by direction and degree (degree 0 is application; the harmonic/crossed
distinction lives in the categories, not the rule), alongside type-raising and
coordination. This is also the node alphabet of `CCG.TargetRestricted.Derivation`. -/
inductive RuleApp where
  /-- Forward generalized composition of degree `n` (`>Bⁿ`; degree 0 is `>`). -/
  | fc (n : Nat)
  /-- Backward generalized composition of degree `n` (`<Bⁿ`; degree 0 is `<`). -/
  | bc (n : Nat)
  /-- Forward type-raising `>T`. -/
  | ftr
  /-- Backward type-raising `<T`. -/
  | btr
  /-- Coordination. -/
  | coord
  deriving DecidableEq, Repr

/-- The rule application is a composition proper: degree at least 1. -/
def RuleApp.IsComp : RuleApp → Prop
  | .fc (_ + 1) => True
  | .bc (_ + 1) => True
  | _ => False

instance : DecidablePred RuleApp.IsComp
  | .fc 0 => isFalse fun h => h
  | .fc (_ + 1) => isTrue trivial
  | .bc 0 => isFalse fun h => h
  | .bc (_ + 1) => isTrue trivial
  | .ftr => isFalse fun h => h
  | .btr => isFalse fun h => h
  | .coord => isFalse fun h => h

/-- The trace of a derivation: the rule applications at its nodes, in preorder. The
structural observables below are read off the trace: `opCount` is its length and
`HasComp` / `HasTypeRaise` are membership. -/
def Derivation.trace {c : Cat α} : Derivation α c → List RuleApp
  | .lex _ _ => []
  | .fapp d1 d2 => .fc 0 :: (d1.trace ++ d2.trace)
  | .bapp d1 d2 => .bc 0 :: (d1.trace ++ d2.trace)
  | .fcomp d1 d2 => .fc 1 :: (d1.trace ++ d2.trace)
  | .bcomp d1 d2 => .bc 1 :: (d1.trace ++ d2.trace)
  | .fcompx d1 d2 => .fc 1 :: (d1.trace ++ d2.trace)
  | .ftr d _ => .ftr :: d.trace
  | .btr d _ => .btr :: d.trace
  | .coord _ d1 d2 => .coord :: (d1.trace ++ d2.trace)

/-- The number of combinatory rule applications in a derivation. -/
def Derivation.opCount {c : Cat α} (d : Derivation α c) : Nat :=
  d.trace.length

/-- The derivation contains a composition node: a rule of degree at least 1 fired. -/
def Derivation.HasComp {c : Cat α} (d : Derivation α c) : Prop :=
  ∃ r ∈ d.trace, r.IsComp

instance {c : Cat α} (d : Derivation α c) : Decidable d.HasComp :=
  inferInstanceAs (Decidable (∃ r ∈ d.trace, r.IsComp))

/-- The derivation contains a type-raising node. -/
def Derivation.HasTypeRaise {c : Cat α} (d : Derivation α c) : Prop :=
  .ftr ∈ d.trace ∨ .btr ∈ d.trace

instance {c : Cat α} (d : Derivation α c) : Decidable d.HasTypeRaise :=
  inferInstanceAs (Decidable (_ ∈ d.trace ∨ _ ∈ d.trace))

end CCG
