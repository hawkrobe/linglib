import Linglib.Syntax.Category.Coordinator

/-!
# Combinatory Categorial Grammar (CCG)

A lexicalized grammar in which categories encode argument structure and a small fixed
set of combinatory rules (`>`, `<`, `B`, `T`, `S`) derive phrases ([steedman-2000]).

## Main definitions

- `CCG.Cat` — categories: atoms plus the directional slashes `/` and `\`
- `CCG.combine` — try every combinatory rule on a pair of categories
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

/-- Forward crossed composition (>B×): X/Y Y\Z => X\Z.

In [steedman-2000] this rule is language-specific and restricted (for Dutch,
to `Y = VP₋SUB`; ch. 6 appendix) — unrestricted crossed composition licenses
scrambling. The toy `Cat` carries no features, so the rule is stated
unrestricted here; the rule-restricted variant lives in
`CCG.Classical.fcompX1`. -/
def forwardCompX : Cat → Cat → Option Cat
  | .rslash x y, .lslash y' z =>
    if y == y' then some (.lslash x z) else none
  | _, _ => none

/-- Try to combine two categories using all available rules. -/
def combine : Cat → Cat → Option Cat
  | c1, c2 =>
    forwardApp c1 c2 <|>
    backwardApp c1 c2 <|>
    forwardComp c1 c2 <|>
    backwardComp c1 c2 <|>
    forwardCompX c1 c2

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
  | fcompx : DerivStep → DerivStep → DerivStep -- forward crossed comp
  | ftr : DerivStep → Cat → DerivStep          -- forward type-raise to target
  | btr : DerivStep → Cat → DerivStep          -- backward type-raise to target
  | coord : Coordinator.Role → DerivStep → DerivStep → DerivStep
      -- coordination (X c X ⇒ X); `c` is the coordinator's role (and/or/but/nor)
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
  | .ftr d t => do
    let x ← d.cat
    some (forwardTypeRaise x t)
  | .btr d t => do
    let x ← d.cat
    some (backwardTypeRaise x t)
  | .coord _ d1 d2 => do
    let c1 ← d1.cat
    let c2 ← d2.cat
    coordinate c1 c2

/-- The surface string a derivation spells out: its leaf forms, left to right.

Combinatory rules concatenate their daughters and type-raising leaves the string
untouched, so the yield is independent of the derivation's combinatory structure —
the property that lets a CCG derivation witness a string language. (Coordination
elides the conjunction's surface form in the yield; `DerivStep.coord` carries the
coordinator's `role`, not its spelled-out word.) -/
def DerivStep.yield : DerivStep → List String
  | .lex e => [e.form]
  | .fapp d1 d2 => d1.yield ++ d2.yield
  | .bapp d1 d2 => d1.yield ++ d2.yield
  | .fcomp d1 d2 => d1.yield ++ d2.yield
  | .bcomp d1 d2 => d1.yield ++ d2.yield
  | .fcompx d1 d2 => d1.yield ++ d2.yield
  | .ftr d _ => d.yield
  | .btr d _ => d.yield
  | .coord _ d1 d2 => d1.yield ++ d2.yield

end Derivations

section Examples

def john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

def sees_mary : DerivStep :=
  .fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩)

def john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) sees_mary

def the_cat : DerivStep :=
  .fapp (.lex ⟨"the", Det⟩) (.lex ⟨"cat", N⟩)

def the_cat_sleeps : DerivStep :=
  .bapp the_cat (.lex ⟨"sleeps", IV⟩)

def big_cat : DerivStep :=
  .fapp (.lex ⟨"big", AdjAttr⟩) (.lex ⟨"cat", N⟩)

def the_big_cat : DerivStep :=
  .fapp (.lex ⟨"the", Det⟩) big_cat

def the_big_cat_sleeps : DerivStep :=
  .bapp the_big_cat (.lex ⟨"sleeps", IV⟩)

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
  | .fcompx d1 d2 => 2 + d1.opCount + d2.opCount
  | .ftr d _ => 1 + d.opCount                     -- type-raising has cost
  | .btr d _ => 1 + d.opCount
  | .coord _ d1 d2 => 1 + d1.opCount + d2.opCount

/-- Depth of derivation tree. -/
def DerivStep.depth : DerivStep → Nat
  | .lex _ => 1
  | .fapp d1 d2 => 1 + max d1.depth d2.depth
  | .bapp d1 d2 => 1 + max d1.depth d2.depth
  | .fcomp d1 d2 => 1 + max d1.depth d2.depth
  | .bcomp d1 d2 => 1 + max d1.depth d2.depth
  | .fcompx d1 d2 => 1 + max d1.depth d2.depth
  | .ftr d _ => 1 + d.depth
  | .btr d _ => 1 + d.depth
  | .coord _ d1 d2 => 1 + max d1.depth d2.depth

example : derivesS john_sleeps = true := rfl
example : derivesS john_sees_mary = true := rfl
example : derivesS the_cat_sleeps = true := rfl
example : derivesS the_big_cat_sleeps = true := rfl

-- The yield reads the surface string off a derivation.
example : john_sees_mary.yield = ["John", "sees", "Mary"] := rfl
example : the_big_cat_sleeps.yield = ["the", "big", "cat", "sleeps"] := rfl

end Examples

section NonConstituentCoordination

def john_tr : DerivStep := .ftr (.lex ⟨"John", NP⟩) S

def john_likes : DerivStep := .fcomp john_tr (.lex ⟨"likes", TV⟩)

def mary_tr : DerivStep := .ftr (.lex ⟨"Mary", NP⟩) S
def mary_hates : DerivStep := .fcomp mary_tr (.lex ⟨"hates", TV⟩)

def john_likes_and_mary_hates : DerivStep := .coord .j john_likes mary_hates

def john_likes_and_mary_hates_beans : DerivStep :=
  .fapp john_likes_and_mary_hates (.lex ⟨"beans", NP⟩)

example : derivesS john_likes_and_mary_hates_beans = true := rfl

-- Non-constituent coordination still spells out the full surface string
-- (the conjunction is elided in the `coord` representation).
example : john_likes_and_mary_hates_beans.yield
            = ["John", "likes", "Mary", "hates", "beans"] := rfl

end NonConstituentCoordination

end CCG
