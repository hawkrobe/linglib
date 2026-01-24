/-
# Combinatory Categorial Grammar (CCG)

CCG is a lexicalized grammar where:
- Categories encode argument structure
- Combinatory rules (>, <, B, T, S) derive phrases
- The syntax-semantics interface is transparent

## Categories

- Atomic: S, NP, N, PP, ...
- Complex: X/Y (looking right for Y), X\Y (looking left for Y)

## Core Rules

- Forward Application (>): X/Y  Y  ⇒  X
- Backward Application (<): Y  X\Y  ⇒  X
- Forward Composition (>B): X/Y  Y/Z  ⇒  X/Z
- Backward Composition (<B): Y\Z  X\Y  ⇒  X\Z

## References

- Steedman (2000). The Syntactic Process.
- Steedman & Baldridge (2011). Combinatory Categorial Grammar.
-/

import LingLean.Syntax.Basic

namespace CCG

-- ============================================================================
-- Categories
-- ============================================================================

/-- Atomic categories -/
inductive Atom where
  | S     -- sentence
  | NP    -- noun phrase
  | N     -- common noun
  | PP    -- prepositional phrase
  deriving Repr, DecidableEq

/-- CCG categories -/
inductive Cat where
  | atom : Atom → Cat
  | rslash : Cat → Cat → Cat  -- X/Y : looking right for Y to give X
  | lslash : Cat → Cat → Cat  -- X\Y : looking left for Y to give X
  deriving Repr, DecidableEq

-- Notation
scoped notation:60 X "/" Y => Cat.rslash X Y
scoped notation:60 X "\\" Y => Cat.lslash X Y

-- Atomic category shortcuts
def S : Cat := .atom .S
def NP : Cat := .atom .NP
def N : Cat := .atom .N
def PP : Cat := .atom .PP

-- ============================================================================
-- Common Category Patterns
-- ============================================================================

-- Intransitive verb: (S\NP) - takes NP on left, gives S
def IV : Cat := S \ NP

-- Transitive verb: (S\NP)/NP - takes NP on right, then NP on left
def TV : Cat := (S \ NP) / NP

-- Ditransitive verb: ((S\NP)/NP)/NP
def DTV : Cat := ((S \ NP) / NP) / NP

-- Determiner: NP/N
def Det : Cat := NP / N

-- Preposition: PP/NP
def Prep : Cat := PP / NP

-- Adjective (attributive): N/N
def AdjAttr : Cat := N / N

-- Adjective (predicative): S\NP (like IV)
def AdjPred : Cat := S \ NP

-- ============================================================================
-- Combinatory Rules
-- ============================================================================

/-- Forward application: X/Y  Y  ⇒  X -/
def forwardApp : Cat → Cat → Option Cat
  | .rslash x y, z => if y == z then some x else none
  | _, _ => none

/-- Backward application: Y  X\Y  ⇒  X -/
def backwardApp : Cat → Cat → Option Cat
  | z, .lslash x y => if y == z then some x else none
  | _, _ => none

/-- Forward composition: X/Y  Y/Z  ⇒  X/Z -/
def forwardComp : Cat → Cat → Option Cat
  | .rslash x y, .rslash y' z =>
    if y == y' then some (.rslash x z) else none
  | _, _ => none

/-- Backward composition: Y\Z  X\Y  ⇒  X\Z -/
def backwardComp : Cat → Cat → Option Cat
  | .lslash y z, .lslash x y' =>
    if y == y' then some (.lslash x z) else none
  | _, _ => none

/-- Try to combine two categories -/
def combine : Cat → Cat → Option Cat
  | c1, c2 =>
    forwardApp c1 c2 <|>
    backwardApp c1 c2 <|>
    forwardComp c1 c2 <|>
    backwardComp c1 c2

-- ============================================================================
-- Lexical Entries
-- ============================================================================

/-- A CCG lexical entry -/
structure LexEntry where
  form : String
  cat : Cat
  deriving Repr

/-- A CCG lexicon -/
def Lexicon := List LexEntry

-- ============================================================================
-- Example Lexicon
-- ============================================================================

def exampleLexicon : Lexicon := [
  -- Proper names: NP
  ⟨"John", NP⟩,
  ⟨"Mary", NP⟩,

  -- Determiners: NP/N
  ⟨"the", Det⟩,
  ⟨"a", Det⟩,
  ⟨"every", Det⟩,

  -- Common nouns: N
  ⟨"cat", N⟩,
  ⟨"dog", N⟩,
  ⟨"book", N⟩,
  ⟨"pizza", N⟩,

  -- Intransitive verbs: S\NP
  ⟨"sleeps", IV⟩,
  ⟨"laughs", IV⟩,
  ⟨"arrives", IV⟩,

  -- Transitive verbs: (S\NP)/NP
  ⟨"sees", TV⟩,
  ⟨"eats", TV⟩,
  ⟨"likes", TV⟩,
  ⟨"reads", TV⟩,

  -- Ditransitive verbs: ((S\NP)/NP)/NP
  ⟨"gives", DTV⟩,

  -- Prepositions: PP/NP
  ⟨"to", Prep⟩,
  ⟨"on", Prep⟩,

  -- Adjectives (attributive): N/N
  ⟨"big", AdjAttr⟩,
  ⟨"happy", AdjAttr⟩
]

-- ============================================================================
-- Derivations
-- ============================================================================

/-- A derivation step -/
inductive DerivStep where
  | lex : LexEntry → DerivStep
  | fapp : DerivStep → DerivStep → DerivStep   -- forward app
  | bapp : DerivStep → DerivStep → DerivStep   -- backward app
  | fcomp : DerivStep → DerivStep → DerivStep  -- forward comp
  | bcomp : DerivStep → DerivStep → DerivStep  -- backward comp
  deriving Repr

/-- Get the category of a derivation -/
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

-- ============================================================================
-- Example Derivations
-- ============================================================================

-- "John sleeps"
-- John:NP  sleeps:S\NP  ⇒  S  (backward application)
def john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

#eval john_sleeps.cat  -- some S ✓

-- "John sees Mary"
-- John:NP  sees:(S\NP)/NP  Mary:NP
-- First: sees Mary ⇒ S\NP (forward app)
-- Then: John (S\NP) ⇒ S (backward app)
def sees_mary : DerivStep :=
  .fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩)

def john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) sees_mary

#eval sees_mary.cat        -- some (S\NP) ✓
#eval john_sees_mary.cat   -- some S ✓

-- "the cat sleeps"
-- the:NP/N  cat:N  ⇒  NP (forward app)
-- NP  sleeps:S\NP  ⇒  S (backward app)
def the_cat : DerivStep :=
  .fapp (.lex ⟨"the", Det⟩) (.lex ⟨"cat", N⟩)

def the_cat_sleeps : DerivStep :=
  .bapp the_cat (.lex ⟨"sleeps", IV⟩)

#eval the_cat.cat         -- some NP ✓
#eval the_cat_sleeps.cat  -- some S ✓

-- "the big cat sleeps"
-- the:NP/N  big:N/N  cat:N
-- big cat ⇒ N (forward app)
-- the (big cat) ⇒ NP (forward app)
-- NP sleeps ⇒ S (backward app)
def big_cat : DerivStep :=
  .fapp (.lex ⟨"big", AdjAttr⟩) (.lex ⟨"cat", N⟩)

def the_big_cat : DerivStep :=
  .fapp (.lex ⟨"the", Det⟩) big_cat

def the_big_cat_sleeps : DerivStep :=
  .bapp the_big_cat (.lex ⟨"sleeps", IV⟩)

#eval big_cat.cat              -- some N ✓
#eval the_big_cat.cat          -- some NP ✓
#eval the_big_cat_sleeps.cat   -- some S ✓

-- ============================================================================
-- Derivation Yields Sentence
-- ============================================================================

/-- Check if a derivation yields category S -/
def derivesS (d : DerivStep) : Bool :=
  d.cat == some S

example : derivesS john_sleeps = true := rfl
example : derivesS john_sees_mary = true := rfl
example : derivesS the_cat_sleeps = true := rfl
example : derivesS the_big_cat_sleeps = true := rfl

end CCG
