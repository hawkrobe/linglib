import Linglib.Syntax.Category.Coordinator

/-!
# Combinatory Categorial Grammar (CCG)

A lexicalized grammar in which categories encode argument structure and a small fixed
set of combinatory rules derives phrases ([steedman-2000]): forward and backward
application (`>`, `<`), harmonic composition (`B`), forward crossed composition (`>B×`),
type-raising (`T`), and the coordination schema. Backward crossed composition and the
substitution rules of [steedman-2000] are not part of this toy inventory; the
target-restricted (VW-CCG) rules live in `CCG.TargetRestricted`.

Categories and rules are stated over an arbitrary type `α` of atomic categories, so a
grammar needing featured atoms (e.g. [steedman-2000]'s `S₊SUB`, `VP₋SUB` for Dutch) can
instantiate a richer inventory. `CCG.Atom` is the featureless toy inventory the English
fragment and the worked studies use.

## Main definitions

- `CCG.Cat` — categories over an atom type: atoms plus the directional slashes `/` and `\`
- `CCG.forwardApp`, `backwardApp`, `forwardComp`, `backwardComp`, `forwardCompX` —
  the combinatory rules as partial operations on categories
- `CCG.DerivStep` — a derivation tree; `DerivStep.cat` reads off its category and
  `DerivStep.yield` the surface string it spells out

## Notation

`/` and `\` build directional slash categories. Because `/` overloads Lean's
division, categories are written fully parenthesized (`(S \ NP) / NP`) rather than
relying on the Steedman left-to-right reading.
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

section CombinatoryRules

/-- Generalized forward composition `>Bⁿ`, the rule schema of
[vijay-shanker-weir-1994] and [steedman-2000]: `X/Y Y|Z₁…|Zₙ ⇒ X|Z₁…|Zₙ`, peeling
the secondary input's last `n` arguments — each keeping its own slash direction, the
Principle of Inheritance — and matching the remainder against `Y`. Degree 0 is forward
application; at degree ≥ 1 the harmonic and crossed instances fall out of the slash
directions rather than being separate rule classes. -/
def forwardCompN : Nat → Cat α → Cat α → Option (Cat α)
  | 0, .rslash x y, z => if y = z then some x else none
  | n + 1, f, .rslash g z => (forwardCompN n f g).map (Cat.rslash · z)
  | n + 1, f, .lslash g z => (forwardCompN n f g).map (Cat.lslash · z)
  | _, _, _ => none

/-- Generalized backward composition `<Bⁿ`: `Y|Z₁…|Zₙ X\Y ⇒ X|Z₁…|Zₙ`, the mirror of
`forwardCompN`. Degree 0 is backward application. -/
def backwardCompN : Nat → Cat α → Cat α → Option (Cat α)
  | 0, z, .lslash x y => if y = z then some x else none
  | n + 1, .rslash g z, f => (backwardCompN n g f).map (Cat.rslash · z)
  | n + 1, .lslash g z, f => (backwardCompN n g f).map (Cat.lslash · z)
  | _, _, _ => none

/-- Forward application `>`: X/Y Y ⇒ X — degree 0 of `forwardCompN`. -/
def forwardApp : Cat α → Cat α → Option (Cat α) := forwardCompN 0

/-- Backward application `<`: Y X\Y ⇒ X — degree 0 of `backwardCompN`. -/
def backwardApp : Cat α → Cat α → Option (Cat α) := backwardCompN 0

/-- Forward harmonic composition `>B`: X/Y Y/Z ⇒ X/Z — the degree-1 harmonic instance
of `forwardCompN` (the toy grammar admits this but not its degree-1 backward crossed
mirror). -/
def forwardComp : Cat α → Cat α → Option (Cat α)
  | f, g@(.rslash _ _) => forwardCompN 1 f g
  | _, _ => none

/-- Backward harmonic composition `<B`: Y\Z X\Y ⇒ X\Z — the degree-1 harmonic instance
of `backwardCompN`. -/
def backwardComp : Cat α → Cat α → Option (Cat α)
  | f@(.lslash _ _), g => backwardCompN 1 f g
  | _, _ => none

/-- Forward crossed composition `>B×`: X/Y Y\Z ⇒ X\Z — the degree-1 crossed instance
of `forwardCompN`.

In [steedman-2000] this rule is language-specific and restricted (for Dutch,
to `Y = VP₋SUB`; ch. 6 appendix) — unrestricted crossed composition licenses
scrambling. The restriction is expressible over a featured atom type; the toy
`Atom` inventory carries no features, and the target-restricted schema lives in
`CCG.TargetRestricted`. -/
def forwardCompX : Cat α → Cat α → Option (Cat α)
  | f, g@(.lslash _ _) => forwardCompN 1 f g
  | _, _ => none

end CombinatoryRules

section TypeRaising

/-- Forward type-raising: X => T/(T\X). -/
def forwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t / (t \ x)

/-- Backward type-raising: X => T\(T/X). -/
def backwardTypeRaise (x : Cat α) (t : Cat α) : Cat α :=
  t \ (t / x)

end TypeRaising

/-- Coordination: X conj X => X. -/
def coordinate : Cat α → Cat α → Option (Cat α)
  | x, y => if x = y then some x else none

/-- A CCG lexical entry. -/
structure LexEntry (α : Type*) where
  form : String
  cat : Cat α
  deriving Repr

section Derivations

/-- A derivation step. -/
inductive DerivStep (α : Type*) where
  /-- A lexical leaf. -/
  | lex : LexEntry α → DerivStep α
  /-- Forward application. -/
  | fapp : DerivStep α → DerivStep α → DerivStep α
  /-- Backward application. -/
  | bapp : DerivStep α → DerivStep α → DerivStep α
  /-- Forward composition. -/
  | fcomp : DerivStep α → DerivStep α → DerivStep α
  /-- Backward composition. -/
  | bcomp : DerivStep α → DerivStep α → DerivStep α
  /-- Forward crossed composition. -/
  | fcompx : DerivStep α → DerivStep α → DerivStep α
  /-- Forward type-raising to a target category. -/
  | ftr : DerivStep α → Cat α → DerivStep α
  /-- Backward type-raising to a target category. -/
  | btr : DerivStep α → Cat α → DerivStep α
  /-- Coordination (X c X ⇒ X). Carries the coordinator itself: its `role` fixes the
      semantic operation (`DerivStep.interp`) and its `form` is spelled out in the yield. -/
  | coord : Coordinator → DerivStep α → DerivStep α → DerivStep α
  deriving Repr

/-- Get the category of a derivation. -/
def DerivStep.cat : DerivStep α → Option (Cat α)
  | .lex e => some e.cat
  | .fapp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardApp c1 c2
  | .bapp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    backwardApp c1 c2
  | .fcomp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardComp c1 c2
  | .bcomp d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    backwardComp c1 c2
  | .fcompx d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    forwardCompX c1 c2
  | .ftr d t => d.cat.map (forwardTypeRaise · t)
  | .btr d t => d.cat.map (backwardTypeRaise · t)
  | .coord _ d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    coordinate c1 c2

/-- The surface string a derivation spells out: its leaf forms and coordinators, left
to right.

Combinatory rules concatenate their daughters and type-raising leaves the string
untouched, so the yield is independent of the derivation's combinatory structure —
the property that lets a CCG derivation witness a string language. -/
def DerivStep.yield : DerivStep α → List String
  | .lex e => [e.form]
  | .fapp d1 d2 | .bapp d1 d2 | .fcomp d1 d2 | .bcomp d1 d2 | .fcompx d1 d2 =>
    d1.yield ++ d2.yield
  | .ftr d _ | .btr d _ => d.yield
  | .coord c d1 d2 => d1.yield ++ c.form :: d2.yield

/-- The number of combinatory rule applications in a derivation. -/
def DerivStep.opCount : DerivStep α → Nat
  | .lex _ => 0
  | .fapp d1 d2 | .bapp d1 d2 | .fcomp d1 d2 | .bcomp d1 d2 | .fcompx d1 d2
  | .coord _ d1 d2 => 1 + d1.opCount + d2.opCount
  | .ftr d _ | .btr d _ => 1 + d.opCount

end Derivations

section Examples

-- "John sees Mary": forward then backward application derives S.
example :
    (DerivStep.bapp (.lex ⟨"John", NP⟩)
      (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))).cat = some S := rfl

-- Type-raising a subject: NP ⇒ S/(S\NP).
example : (DerivStep.ftr (.lex ⟨"John", NP⟩) S).cat = some (S / (S \ NP)) := rfl

-- The yield spells out the surface string, coordinator included.
example :
    (DerivStep.coord { form := "and", gloss := "and", role := .j, kind := .free }
      (.bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩))
      (.bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"laughs", IV⟩))).yield
      = ["John", "sleeps", "and", "Mary", "laughs"] := rfl

end Examples

end CCG
