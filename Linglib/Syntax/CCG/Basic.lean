import Linglib.Syntax.Category.Coordinator

/-!
# Combinatory Categorial Grammar (CCG)

A lexicalized grammar in which categories encode argument structure and a small fixed
set of combinatory rules derives phrases ([steedman-2000]): forward and backward
application (`>`, `<`), harmonic composition (`B`), forward crossed composition (`>B×`),
type-raising (`T`), and the coordination schema. Backward crossed composition and the
substitution rules of [steedman-2000] are not part of this toy inventory; the
rule-restricted (classical) rules live in `CCG.Classical`.

## Main definitions

- `CCG.Cat` — categories: atoms plus the directional slashes `/` and `\`
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

/-- Atomic categories. -/
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

/-- CCG categories. -/
inductive Cat where
  /-- An atomic category. -/
  | atom : Atom → Cat
  /-- `X/Y`: looking right for a `Y` to give an `X`. -/
  | rslash : Cat → Cat → Cat
  /-- `X\Y`: looking left for a `Y` to give an `X`. -/
  | lslash : Cat → Cat → Cat
  deriving Repr, DecidableEq

scoped notation:60 X "/" Y => Cat.rslash X Y
scoped notation:60 X "\\" Y => Cat.lslash X Y

def S : Cat := .atom .S
def NP : Cat := .atom .NP
def N : Cat := .atom .N
def PP : Cat := .atom .PP

def IV : Cat := S \ NP
def TV : Cat := (S \ NP) / NP
def Det : Cat := NP / N

end Categories

section CombinatoryRules

/-- Forward application: X/Y Y => X. -/
def forwardApp : Cat → Cat → Option Cat
  | .rslash x y, z => if y = z then some x else none
  | _, _ => none

/-- Backward application: Y X\Y => X. -/
def backwardApp : Cat → Cat → Option Cat
  | z, .lslash x y => if y = z then some x else none
  | _, _ => none

/-- Forward composition: X/Y Y/Z => X/Z. -/
def forwardComp : Cat → Cat → Option Cat
  | .rslash x y, .rslash y' z =>
    if y = y' then some (.rslash x z) else none
  | _, _ => none

/-- Backward composition: Y\Z X\Y => X\Z. -/
def backwardComp : Cat → Cat → Option Cat
  | .lslash y z, .lslash x y' =>
    if y = y' then some (.lslash x z) else none
  | _, _ => none

/-- Forward crossed composition (>B×): X/Y Y\Z => X\Z.

In [steedman-2000] this rule is language-specific and restricted (for Dutch,
to `Y = VP₋SUB`; ch. 6 appendix) — unrestricted crossed composition licenses
scrambling. The toy `Cat` carries no features, so the rule is stated
unrestricted here; the rule-restricted variant lives in
`CCG.Classical.fcompX1`. -/
def forwardCompX : Cat → Cat → Option Cat
  | .rslash x y, .lslash y' z =>
    if y = y' then some (.lslash x z) else none
  | _, _ => none

end CombinatoryRules

section TypeRaising

/-- Forward type-raising: X => T/(T\X). -/
def forwardTypeRaise (x : Cat) (t : Cat) : Cat :=
  t / (t \ x)

/-- Backward type-raising: X => T\(T/X). -/
def backwardTypeRaise (x : Cat) (t : Cat) : Cat :=
  t \ (t / x)

end TypeRaising

/-- Coordination: X conj X => X. -/
def coordinate : Cat → Cat → Option Cat
  | x, y => if x = y then some x else none

/-- A CCG lexical entry. -/
structure LexEntry where
  form : String
  cat : Cat
  deriving Repr

section Derivations

/-- A derivation step. -/
inductive DerivStep where
  /-- A lexical leaf. -/
  | lex : LexEntry → DerivStep
  /-- Forward application. -/
  | fapp : DerivStep → DerivStep → DerivStep
  /-- Backward application. -/
  | bapp : DerivStep → DerivStep → DerivStep
  /-- Forward composition. -/
  | fcomp : DerivStep → DerivStep → DerivStep
  /-- Backward composition. -/
  | bcomp : DerivStep → DerivStep → DerivStep
  /-- Forward crossed composition. -/
  | fcompx : DerivStep → DerivStep → DerivStep
  /-- Forward type-raising to a target category. -/
  | ftr : DerivStep → Cat → DerivStep
  /-- Backward type-raising to a target category. -/
  | btr : DerivStep → Cat → DerivStep
  /-- Coordination (X c X ⇒ X). Carries the coordinator itself: its `role` fixes the
      semantic operation (`DerivStep.interp`) and its `form` is spelled out in the yield. -/
  | coord : Coordinator → DerivStep → DerivStep → DerivStep
  deriving Repr

/-- Get the category of a derivation. -/
def DerivStep.cat : DerivStep → Option Cat
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
def DerivStep.yield : DerivStep → List String
  | .lex e => [e.form]
  | .fapp d1 d2 | .bapp d1 d2 | .fcomp d1 d2 | .bcomp d1 d2 | .fcompx d1 d2 =>
    d1.yield ++ d2.yield
  | .ftr d _ | .btr d _ => d.yield
  | .coord c d1 d2 => d1.yield ++ c.form :: d2.yield

/-- The number of combinatory rule applications in a derivation. -/
def DerivStep.opCount : DerivStep → Nat
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
