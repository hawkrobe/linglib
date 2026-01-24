/-
# Montague-Style Compositional Semantics

A simple model-theoretic semantics demonstrating the syntax-semantics interface.

## Semantic Types

Following Montague:
- `e` : entities (individuals)
- `t` : truth values
- `e → t` : properties (intransitive verbs, common nouns)
- `e → e → t` : relations (transitive verbs)
- `(e → t) → t` : generalized quantifiers (DPs)

## Composition

The meaning of a phrase is computed from its parts:
- Function application: if α has type σ → τ and β has type σ, then ⟦α β⟧ = ⟦α⟧(⟦β⟧)
-/

import LingLean.Core.Basic

namespace Montague

-- ============================================================================
-- Semantic Types
-- ============================================================================

/-- Semantic types -/
inductive Ty where
  | e    -- entities
  | t    -- truth values
  | fn : Ty → Ty → Ty  -- function types
  deriving Repr, DecidableEq

infixr:25 " ⇒ " => Ty.fn

-- Common type abbreviations
def Ty.et : Ty := .e ⇒ .t           -- properties
def Ty.eet : Ty := .e ⇒ .e ⇒ .t     -- relations
def Ty.ett : Ty := (.e ⇒ .t) ⇒ .t   -- generalized quantifiers

-- ============================================================================
-- Models
-- ============================================================================

/-- A model provides a domain and interpretations -/
structure Model where
  /-- The domain of entities -/
  Entity : Type
  /-- Decidable equality on entities -/
  decEq : DecidableEq Entity

/-- Interpretation of types in a model -/
def Model.interpTy (m : Model) : Ty → Type
  | .e => m.Entity
  | .t => Bool
  | .fn σ τ => m.interpTy σ → m.interpTy τ

-- ============================================================================
-- A Toy Model
-- ============================================================================

/-- A small domain for examples -/
inductive ToyEntity where
  | john
  | mary
  | pizza
  | book
  deriving Repr, DecidableEq

/-- The toy model -/
def toyModel : Model := {
  Entity := ToyEntity
  decEq := inferInstance
}

-- ============================================================================
-- Lexical Semantics
-- ============================================================================

/-- Lexical entries map words to their denotations -/
structure LexEntry (m : Model) where
  ty : Ty
  denot : m.interpTy ty

/-- A lexicon is a partial function from word forms to entries -/
def Lexicon (m : Model) := String → Option (LexEntry m)

-- ============================================================================
-- Toy Lexicon
-- ============================================================================

namespace ToyLexicon

open ToyEntity

-- Proper names denote entities
def john_sem : toyModel.interpTy .e := ToyEntity.john
def mary_sem : toyModel.interpTy .e := ToyEntity.mary

-- Intransitive verbs denote properties (e → t)
def sleeps_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .john => true
    | .mary => false
    | _ => false

def laughs_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .john => true
    | .mary => true
    | _ => false

-- Transitive verbs denote relations (e → e → t)
-- "sees" takes object first, then subject: λy.λx. x sees y
def sees_sem : toyModel.interpTy (.e ⇒ .e ⇒ .t) :=
  fun obj => fun subj => match subj, obj with
    | .john, .mary => true
    | .mary, .john => true
    | _, _ => false

def eats_sem : toyModel.interpTy (.e ⇒ .e ⇒ .t) :=
  fun obj => fun subj => match subj, obj with
    | .john, .pizza => true
    | .mary, .pizza => true
    | _, _ => false

def reads_sem : toyModel.interpTy (.e ⇒ .e ⇒ .t) :=
  fun obj => fun subj => match subj, obj with
    | .john, .book => true
    | .mary, .book => true
    | _, _ => false

-- Common nouns denote properties
def pizza_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .pizza => true
    | _ => false

def book_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .book => true
    | _ => false

end ToyLexicon

-- ============================================================================
-- Composition
-- ============================================================================

/-- Function application (the core composition rule) -/
def apply {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) : m.interpTy τ :=
  f x

-- ============================================================================
-- Example Derivations
-- ============================================================================

open ToyLexicon

-- "John sleeps" = sleeps(john) = true
#eval apply sleeps_sem john_sem  -- true

-- "Mary sleeps" = sleeps(mary) = false
#eval apply sleeps_sem mary_sem  -- false

-- "John laughs" = laughs(john) = true
#eval apply laughs_sem john_sem  -- true

-- "Mary laughs" = laughs(mary) = true
#eval apply laughs_sem mary_sem  -- true

-- "John sees Mary" = sees(mary)(john) = true
-- First: apply sees to object (Mary)
-- Then: apply result to subject (John)
#eval apply (apply sees_sem mary_sem) john_sem  -- true

-- "Mary sees John" = sees(john)(mary) = true
#eval apply (apply sees_sem john_sem) mary_sem  -- true

-- "John sees John" = sees(john)(john) = false
#eval apply (apply sees_sem john_sem) john_sem  -- false

-- "John eats pizza" = eats(pizza)(john) = true
#eval apply (apply eats_sem ToyEntity.pizza) john_sem  -- true

-- "John eats Mary" = eats(mary)(john) = false
#eval apply (apply eats_sem mary_sem) john_sem  -- false

-- ============================================================================
-- Connecting to Syntactic Derivations
-- ============================================================================

/-- A semantic derivation pairs a syntactic structure with its meaning -/
structure SemanticDeriv (m : Model) where
  words : List Word
  ty : Ty
  meaning : m.interpTy ty

/-- Interpret a subject-verb sentence -/
def interpSV (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .t)) : m.interpTy .t :=
  apply verb subj

/-- Interpret a subject-verb-object sentence -/
def interpSVO (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (obj : m.interpTy .e) : m.interpTy .t :=
  apply (apply verb obj) subj

-- ============================================================================
-- Truth Conditions
-- ============================================================================

/-- A sentence is true in a model if its denotation is true -/
def isTrue (m : Model) (meaning : m.interpTy .t) : Prop :=
  meaning = true

-- Examples
example : isTrue toyModel (interpSV toyModel john_sem sleeps_sem) := rfl
example : isTrue toyModel (interpSVO toyModel john_sem eats_sem ToyEntity.pizza) := rfl

-- Counter-examples (these would NOT be provable)
-- example : isTrue toyModel (interpSV toyModel mary_sem sleeps_sem) := rfl  -- would fail

-- ============================================================================
-- Connecting to the SemanticBackend Interface
-- ============================================================================

/-
A model-theoretic semantics provides a SemanticBackend.
The agreement function φ is 1 if true, 0 if false.
(This would require importing SemanticBackend and more setup)
-/

end Montague
