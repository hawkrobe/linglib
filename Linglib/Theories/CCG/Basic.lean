/-
# Combinatory Categorial Grammar (CCG)

Lexicalized grammar with categories encoding argument structure and
combinatory rules (>, <, B, T, S) deriving phrases.

- Steedman (2000). The Syntactic Process.
- Steedman & Baldridge (2011). Combinatory Categorial Grammar.
-/

import Linglib.Core.Basic

namespace CCG

section Categories

/-- Atomic categories. -/
inductive Atom where
  | S     -- sentence
  | NP    -- noun phrase
  | N     -- common noun
  | PP    -- prepositional phrase
  deriving Repr, DecidableEq

/-- CCG categories. -/
inductive Cat where
  | atom : Atom → Cat
  | rslash : Cat → Cat → Cat  -- X/Y : looking right for Y to give X
  | lslash : Cat → Cat → Cat  -- X\Y : looking left for Y to give X
  deriving Repr, DecidableEq

scoped notation:60 X "/" Y => Cat.rslash X Y
scoped notation:60 X "\\" Y => Cat.lslash X Y

def S : Cat := .atom .S
def NP : Cat := .atom .NP
def N : Cat := .atom .N
def PP : Cat := .atom .PP

def IV : Cat := S \ NP
def TV : Cat := (S \ NP) / NP
def DTV : Cat := ((S \ NP) / NP) / NP
def Det : Cat := NP / N
def Prep : Cat := PP / NP
def AdjAttr : Cat := N / N
def AdjPred : Cat := S \ NP

end Categories

section CombinatoryRules

/-- Forward application: X/Y Y => X. -/
def forwardApp : Cat → Cat → Option Cat
  | .rslash x y, z => if y == z then some x else none
  | _, _ => none

/-- Backward application: Y X\Y => X. -/
def backwardApp : Cat → Cat → Option Cat
  | z, .lslash x y => if y == z then some x else none
  | _, _ => none

/-- Forward composition: X/Y Y/Z => X/Z. -/
def forwardComp : Cat → Cat → Option Cat
  | .rslash x y, .rslash y' z =>
    if y == y' then some (.rslash x z) else none
  | _, _ => none

/-- Backward composition: Y\Z X\Y => X\Z. -/
def backwardComp : Cat → Cat → Option Cat
  | .lslash y z, .lslash x y' =>
    if y == y' then some (.lslash x z) else none
  | _, _ => none

/-- Try to combine two categories using all available rules. -/
def combine : Cat → Cat → Option Cat
  | c1, c2 =>
    forwardApp c1 c2 <|>
    backwardApp c1 c2 <|>
    forwardComp c1 c2 <|>
    backwardComp c1 c2

end CombinatoryRules

section TypeRaising

/-- Forward type-raising: X => T/(T\X). -/
def forwardTypeRaise (x : Cat) (t : Cat) : Cat :=
  t / (t \ x)

/-- Backward type-raising: X => T\(T/X). -/
def backwardTypeRaise (x : Cat) (t : Cat) : Cat :=
  t \ (t / x)

def NPsubj : Cat := forwardTypeRaise NP S
def NPobj : Cat := backwardTypeRaise NP S

#eval NPsubj

end TypeRaising

/-- Coordination: X conj X => X. -/
def coordinate : Cat → Cat → Option Cat
  | x, y => if x == y then some x else none

/-- A CCG lexical entry. -/
structure LexEntry where
  form : String
  cat : Cat
  deriving Repr

/-- A CCG lexicon. -/
def Lexicon := List LexEntry

def exampleLexicon : Lexicon := [
  ⟨"John", NP⟩, ⟨"Mary", NP⟩,
  ⟨"the", Det⟩, ⟨"a", Det⟩, ⟨"every", Det⟩,
  ⟨"cat", N⟩, ⟨"dog", N⟩, ⟨"book", N⟩, ⟨"pizza", N⟩, ⟨"beans", NP⟩,
  ⟨"sleeps", IV⟩, ⟨"laughs", IV⟩, ⟨"arrives", IV⟩,
  ⟨"sees", TV⟩, ⟨"eats", TV⟩, ⟨"likes", TV⟩, ⟨"hates", TV⟩, ⟨"reads", TV⟩,
  ⟨"gives", DTV⟩,
  ⟨"to", Prep⟩, ⟨"on", Prep⟩,
  ⟨"big", AdjAttr⟩, ⟨"happy", AdjAttr⟩
]

section Derivations

/-- A derivation step. -/
inductive DerivStep where
  | lex : LexEntry → DerivStep
  | fapp : DerivStep → DerivStep → DerivStep   -- forward app
  | bapp : DerivStep → DerivStep → DerivStep   -- backward app
  | fcomp : DerivStep → DerivStep → DerivStep  -- forward comp
  | bcomp : DerivStep → DerivStep → DerivStep  -- backward comp
  | ftr : DerivStep → Cat → DerivStep          -- forward type-raise to target
  | btr : DerivStep → Cat → DerivStep          -- backward type-raise to target
  | coord : DerivStep → DerivStep → DerivStep  -- coordination (X and X ⇒ X)
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
  | .ftr d t => do
    let x ← d.cat
    some (forwardTypeRaise x t)
  | .btr d t => do
    let x ← d.cat
    some (backwardTypeRaise x t)
  | .coord d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    coordinate c1 c2

end Derivations

section Examples

def john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

#eval john_sleeps.cat
def sees_mary : DerivStep :=
  .fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩)

def john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) sees_mary

#eval sees_mary.cat
#eval john_sees_mary.cat
def the_cat : DerivStep :=
  .fapp (.lex ⟨"the", Det⟩) (.lex ⟨"cat", N⟩)

def the_cat_sleeps : DerivStep :=
  .bapp the_cat (.lex ⟨"sleeps", IV⟩)

#eval the_cat.cat
#eval the_cat_sleeps.cat
def big_cat : DerivStep :=
  .fapp (.lex ⟨"big", AdjAttr⟩) (.lex ⟨"cat", N⟩)

def the_big_cat : DerivStep :=
  .fapp (.lex ⟨"the", Det⟩) big_cat

def the_big_cat_sleeps : DerivStep :=
  .bapp the_big_cat (.lex ⟨"sleeps", IV⟩)

#eval big_cat.cat
#eval the_big_cat.cat
#eval the_big_cat_sleeps.cat

/-- Check if a derivation yields category S. -/
def derivesS (d : DerivStep) : Bool :=
  d.cat == some S

/-- Count combinatory operations in a derivation. -/
def DerivStep.opCount : DerivStep → Nat
  | .lex _ => 0
  | .fapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .bapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .fcomp d1 d2 => 2 + d1.opCount + d2.opCount   -- composition is "harder"
  | .bcomp d1 d2 => 2 + d1.opCount + d2.opCount
  | .ftr d _ => 1 + d.opCount                     -- type-raising has cost
  | .btr d _ => 1 + d.opCount
  | .coord d1 d2 => 1 + d1.opCount + d2.opCount

/-- Depth of derivation tree. -/
def DerivStep.depth : DerivStep → Nat
  | .lex _ => 1
  | .fapp d1 d2 => 1 + max d1.depth d2.depth
  | .bapp d1 d2 => 1 + max d1.depth d2.depth
  | .fcomp d1 d2 => 1 + max d1.depth d2.depth
  | .bcomp d1 d2 => 1 + max d1.depth d2.depth
  | .ftr d _ => 1 + d.depth
  | .btr d _ => 1 + d.depth
  | .coord d1 d2 => 1 + max d1.depth d2.depth

example : derivesS john_sleeps = true := rfl
example : derivesS john_sees_mary = true := rfl
example : derivesS the_cat_sleeps = true := rfl
example : derivesS the_big_cat_sleeps = true := rfl

end Examples

section NonConstituentCoordination

def john_tr : DerivStep := .ftr (.lex ⟨"John", NP⟩) S

#eval john_tr.cat
def john_likes : DerivStep := .fcomp john_tr (.lex ⟨"likes", TV⟩)

#eval john_likes.cat
def mary_tr : DerivStep := .ftr (.lex ⟨"Mary", NP⟩) S
def mary_hates : DerivStep := .fcomp mary_tr (.lex ⟨"hates", TV⟩)

#eval mary_hates.cat
def john_likes_and_mary_hates : DerivStep := .coord john_likes mary_hates

#eval john_likes_and_mary_hates.cat
def john_likes_and_mary_hates_beans : DerivStep :=
  .fapp john_likes_and_mary_hates (.lex ⟨"beans", NP⟩)

#eval john_likes_and_mary_hates_beans.cat

example : derivesS john_likes_and_mary_hates_beans = true := rfl

end NonConstituentCoordination

end CCG
