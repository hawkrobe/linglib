/-
# CCG Syntax-Semantics Interface

The key insight of CCG: syntactic categories directly encode semantic types.

- NP corresponds to type e (entities)
- S corresponds to type t (truth values)
- X/Y corresponds to type ⟦Y⟧ → ⟦X⟧
- X\Y corresponds to type ⟦Y⟧ → ⟦X⟧

Combinatory rules correspond to function application/composition.
-/

import LingLean.Syntax.CCG.Basic
import LingLean.Semantics.Montague

namespace CCG

open Semantics

-- ============================================================================
-- Type Correspondence
-- ============================================================================

/-- Map CCG categories to semantic types -/
def catToTy : Cat → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x y => catToTy y ⇒ catToTy x
  | .lslash x y => catToTy y ⇒ catToTy x

-- Verify the type correspondence
#eval catToTy S            -- t
#eval catToTy NP           -- e
#eval catToTy N            -- e ⇒ t
#eval catToTy IV           -- e ⇒ t (same as N, both are properties)
#eval catToTy TV           -- e ⇒ e ⇒ t (relations)
#eval catToTy Det          -- (e ⇒ t) ⇒ e (simplified)

-- ============================================================================
-- Semantic Lexicon
-- ============================================================================

/-- A CCG lexical entry with semantics -/
structure SemLexEntry (m : Model) where
  form : String
  cat : Cat
  sem : m.interpTy (catToTy cat)

/-- Semantic lexicon for the toy model -/
def semLexicon : List (SemLexEntry toyModel) := [
  -- Proper names: NP (type e)
  ⟨"John", NP, ToyEntity.john⟩,
  ⟨"Mary", NP, ToyEntity.mary⟩,

  -- Intransitive verbs: S\NP (type e → t)
  ⟨"sleeps", IV, ToyLexicon.sleeps_sem⟩,
  ⟨"laughs", IV, ToyLexicon.laughs_sem⟩,

  -- Transitive verbs: (S\NP)/NP (type e → e → t)
  ⟨"sees", TV, ToyLexicon.sees_sem⟩,
  ⟨"eats", TV, ToyLexicon.eats_sem⟩,
  ⟨"reads", TV, ToyLexicon.reads_sem⟩
]

-- ============================================================================
-- Semantic Composition
-- ============================================================================

-- Forward application semantically is just function application
-- If f : ⟦Y⟧ → ⟦X⟧ and a : ⟦Y⟧, then f(a) : ⟦X⟧

-- Backward application is the same
-- If a : ⟦Y⟧ and f : ⟦Y⟧ → ⟦X⟧, then f(a) : ⟦X⟧

-- ============================================================================
-- Example: "John sleeps"
-- ============================================================================

-- Syntactically: John:NP  sleeps:S\NP  ⇒  S
-- Semantically: sleeps_sem(john_sem) : t

def john_sem' : toyModel.interpTy (catToTy NP) := ToyEntity.john
def sleeps_sem' : toyModel.interpTy (catToTy IV) := ToyLexicon.sleeps_sem

-- The semantic derivation mirrors the syntactic one
def john_sleeps_sem : toyModel.interpTy (catToTy S) :=
  sleeps_sem' john_sem'

#eval john_sleeps_sem  -- true

-- ============================================================================
-- Example: "John sees Mary"
-- ============================================================================

-- Syntactically:
--   John:NP  sees:(S\NP)/NP  Mary:NP
--   sees Mary ⇒ S\NP  (forward app)
--   John (sees Mary) ⇒ S  (backward app)

-- Semantically:
--   sees_sem : e → e → t
--   sees_sem(mary) : e → t
--   (sees_sem(mary))(john) : t

def sees_sem' : toyModel.interpTy (catToTy TV) := ToyLexicon.sees_sem
def mary_sem' : toyModel.interpTy (catToTy NP) := ToyEntity.mary

-- Step 1: sees Mary
def sees_mary_sem : toyModel.interpTy (catToTy IV) :=
  sees_sem' mary_sem'  -- function application

-- Step 2: John (sees Mary)
def john_sees_mary_sem : toyModel.interpTy (catToTy S) :=
  sees_mary_sem john_sem'  -- function application

#eval john_sees_mary_sem  -- true

-- ============================================================================
-- Example: "Mary sees John"
-- ============================================================================

def mary_sees_john_sem : toyModel.interpTy (catToTy S) :=
  (sees_sem' john_sem') mary_sem'

#eval mary_sees_john_sem  -- true

-- ============================================================================
-- Example: "John eats pizza"
-- ============================================================================

def eats_sem' : toyModel.interpTy (catToTy TV) := ToyLexicon.eats_sem
def pizza_sem' : toyModel.interpTy (catToTy NP) := ToyEntity.pizza

def john_eats_pizza_sem : toyModel.interpTy (catToTy S) :=
  (eats_sem' pizza_sem') john_sem'

#eval john_eats_pizza_sem  -- true

-- ============================================================================
-- Truth Conditions from CCG Derivations
-- ============================================================================

/-- A sentence is true if its meaning is true -/
def sentenceTrue (meaning : toyModel.interpTy .t) : Prop :=
  meaning = true

-- Prove truth conditions
example : sentenceTrue john_sleeps_sem := rfl
example : sentenceTrue john_sees_mary_sem := rfl
example : sentenceTrue john_eats_pizza_sem := rfl

-- ============================================================================
-- The Key Insight: Derivations Compute Meanings
-- ============================================================================

/-
The CCG derivation structure directly mirrors semantic composition:

Syntax:                    Semantics:
John:NP   sees:(S\NP)/NP   john:e   sees:e→e→t
               |                        |
          Mary:NP                  mary:e
               ↓                        ↓
          sees Mary:S\NP           sees(mary):e→t
               ↓                        ↓
        John sees Mary:S         sees(mary)(john):t

Each syntactic combination corresponds to function application.
This is the "transparency" of the syntax-semantics interface.
-/

end CCG
