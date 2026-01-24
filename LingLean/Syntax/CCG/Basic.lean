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
-- Type-Raising
-- ============================================================================

/-- Forward type-raising: X ⇒ T/(T\X)
    Typically used for subjects: NP ⇒ S/(S\NP) -/
def forwardTypeRaise (x : Cat) (t : Cat) : Cat :=
  t / (t \ x)

/-- Backward type-raising: X ⇒ T\(T/X)
    Typically used for objects: NP ⇒ S\(S/NP) -/
def backwardTypeRaise (x : Cat) (t : Cat) : Cat :=
  t \ (t / x)

-- Common type-raised categories
def NPsubj : Cat := forwardTypeRaise NP S    -- S/(S\NP) - subject
def NPobj : Cat := backwardTypeRaise NP S    -- S\(S/NP) - object (less common)

#eval NPsubj  -- S/(S\NP)

-- ============================================================================
-- Coordination
-- ============================================================================

/-- Coordination: X conj X ⇒ X
    Both conjuncts must have the same category -/
def coordinate : Cat → Cat → Option Cat
  | x, y => if x == y then some x else none

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
  ⟨"beans", NP⟩,  -- bare plural (simplified as NP)

  -- Intransitive verbs: S\NP
  ⟨"sleeps", IV⟩,
  ⟨"laughs", IV⟩,
  ⟨"arrives", IV⟩,

  -- Transitive verbs: (S\NP)/NP
  ⟨"sees", TV⟩,
  ⟨"eats", TV⟩,
  ⟨"likes", TV⟩,
  ⟨"hates", TV⟩,
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
  | ftr : DerivStep → Cat → DerivStep          -- forward type-raise to target
  | btr : DerivStep → Cat → DerivStep          -- backward type-raise to target
  | coord : DerivStep → DerivStep → DerivStep  -- coordination (X and X ⇒ X)
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

-- ============================================================================
-- Derivation Complexity Measures
-- ============================================================================

/-- Count combinatory operations in a derivation -/
def DerivStep.opCount : DerivStep → Nat
  | .lex _ => 0
  | .fapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .bapp d1 d2 => 1 + d1.opCount + d2.opCount
  | .fcomp d1 d2 => 2 + d1.opCount + d2.opCount   -- composition is "harder"
  | .bcomp d1 d2 => 2 + d1.opCount + d2.opCount
  | .ftr d _ => 1 + d.opCount                     -- type-raising has cost
  | .btr d _ => 1 + d.opCount
  | .coord d1 d2 => 1 + d1.opCount + d2.opCount

/-- Depth of derivation tree -/
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

-- ============================================================================
-- Non-Constituent Coordination (Steedman's Classic Example)
-- ============================================================================

/-
"John likes and Mary hates beans"

This is the canonical CCG example where "John likes" and "Mary hates"
are NOT traditional constituents, yet they coordinate.

The derivation requires:
1. Type-raising: NP ⇒ S/(S\NP)
2. Forward composition: S/(S\NP) + (S\NP)/NP ⇒ S/NP
3. Coordination: S/NP conj S/NP ⇒ S/NP
4. Forward application: S/NP + NP ⇒ S

Derivation tree:
         John        likes         and    Mary        hates        beans
          NP      (S\NP)/NP        conj    NP       (S\NP)/NP        NP
          ↓ >T                             ↓ >T
      S/(S\NP)                         S/(S\NP)
          └───────>B──────┘                └───────>B──────┘
               S/NP                             S/NP
               └─────────────Φ──────────────────┘
                            S/NP
                            └──────────────>─────────────────┘
                                            S
-/

-- Step 1: Type-raise John to S/(S\NP)
def john_tr : DerivStep := .ftr (.lex ⟨"John", NP⟩) S

#eval john_tr.cat  -- S/(S\NP) ✓

-- Step 2: Forward compose with "likes" to get S/NP
-- S/(S\NP) + (S\NP)/NP ⇒ S/NP
def john_likes : DerivStep := .fcomp john_tr (.lex ⟨"likes", TV⟩)

#eval john_likes.cat  -- S/NP ✓ (an incomplete sentence looking for object)

-- Step 3: Type-raise Mary and compose with "hates"
def mary_tr : DerivStep := .ftr (.lex ⟨"Mary", NP⟩) S
def mary_hates : DerivStep := .fcomp mary_tr (.lex ⟨"hates", TV⟩)

#eval mary_hates.cat  -- S/NP ✓

-- Step 4: Coordinate "John likes" and "Mary hates"
-- S/NP conj S/NP ⇒ S/NP
def john_likes_and_mary_hates : DerivStep := .coord john_likes mary_hates

#eval john_likes_and_mary_hates.cat  -- S/NP ✓

-- Step 5: Apply to "beans"
def john_likes_and_mary_hates_beans : DerivStep :=
  .fapp john_likes_and_mary_hates (.lex ⟨"beans", NP⟩)

#eval john_likes_and_mary_hates_beans.cat  -- S ✓

-- Verify the full derivation yields S
example : derivesS john_likes_and_mary_hates_beans = true := rfl

/-
Key insight: The "non-constituents" John likes and Mary hates
are actually constituents in CCG! They have category S/NP.
CCG's flexible constituency allows coordination of these phrases.
-/

-- ============================================================================
-- Contrast: Why Standard Phrase Structure Can't Do This
-- ============================================================================

/-
In standard phrase structure grammar:

    [S [NP John] [VP likes [NP ___]]] and [S [NP Mary] [VP hates [NP ___]]] beans

"John likes" is not a constituent - it's NP + part of VP.
Standard coordination requires matching constituents.

CCG solves this by:
1. Making constituency flexible via type-raising
2. Using composition to build partial structures
3. Coordinating those partial structures

This is why CCG is called "mildly context-sensitive" -
it can handle some non-context-free phenomena.
-/

end CCG
