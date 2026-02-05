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

import Linglib.Core.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

namespace Montague

-- Semantic Types

/-- Semantic types (Montague's type theory)

The basic types are:
- `e`: entities (individuals)
- `t`: truth values
- `s`: possible worlds (for intensional semantics)

Complex types are built with `fn` (function types). -/
inductive Ty where
  | e    -- entities
  | t    -- truth values
  | s    -- possible worlds (for intensional semantics)
  | fn : Ty → Ty → Ty  -- function types
  deriving Repr, DecidableEq

infixr:25 " ⇒ " => Ty.fn

-- Common type abbreviations
def Ty.et : Ty := .e ⇒ .t           -- properties
def Ty.eet : Ty := .e ⇒ .e ⇒ .t     -- relations
def Ty.ett : Ty := (.e ⇒ .t) ⇒ .t   -- generalized quantifiers
def Ty.st : Ty := .s ⇒ .t           -- propositions (intensions of t)
def Ty.se : Ty := .s ⇒ .e           -- individual concepts (intensions of e)

-- Models

/-- A model provides a domain of entities and possible worlds.

For intensional semantics, we need both:
- Entity: the domain of individuals
- World: the set of possible worlds

Intensions are functions from worlds to extensions. -/
structure Model where
  /-- The domain of entities -/
  Entity : Type
  /-- The set of possible worlds -/
  World : Type := Unit  -- Default to trivial (extensional) semantics
  /-- Decidable equality on entities -/
  decEq : DecidableEq Entity

/-- Interpretation of types in a model -/
def Model.interpTy (m : Model) : Ty → Type
  | .e => m.Entity
  | .t => Bool
  | .s => m.World
  | .fn σ τ => m.interpTy σ → m.interpTy τ

-- A Toy Model

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

-- Lexical Semantics

/-- Lexical entries map words to their denotations -/
structure LexEntry (m : Model) where
  ty : Ty
  denot : m.interpTy ty

/-- A lexicon is a partial function from word forms to entries -/
def Lexicon (m : Model) := String → Option (LexEntry m)

-- Toy Lexicon

namespace ToyLexicon

open ToyEntity

-- Proper names denote entities
def john_sem : toyModel.interpTy .e := ToyEntity.john
def mary_sem : toyModel.interpTy .e := ToyEntity.mary

-- Intransitive verbs denote properties (e → t)
def sleeps_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .john => true
    | .mary => false
    | _ => false

def laughs_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .john => true
    | .mary => true
    | _ => false

-- Transitive verbs denote relations (e → e → t)
-- "sees" takes object first, then subject: λy.λx. x sees y
def sees_sem : toyModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .mary => true
    | .mary, .john => true
    | _, _ => false

def eats_sem : toyModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .pizza => true
    | .mary, .pizza => true
    | _, _ => false

def reads_sem : toyModel.interpTy (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .book => true
    | .mary, .book => true
    | _, _ => false

-- Common nouns denote properties
def pizza_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .pizza => true
    | _ => false

def book_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .book => true
    | _ => false

end ToyLexicon

-- Composition

/-- Function application (the core composition rule) -/
def apply {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) : m.interpTy τ :=
  f x

-- Connecting to Syntactic Derivations

open ToyLexicon

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

-- Sentence-Level Logical Operators

/-- Sentence negation: ¬p
    Type: t → t
    "John doesn't sleep" = neg(sleep(john))

    This is the model-theoretic version (operates on a single Bool).
    For the world-indexed version with proven DE property, see
    `Core.Proposition.Decidable.pnot`.

    Connection: `pnot W p w = neg (p w)` -/
def neg {m : Model} (p : m.interpTy .t) : m.interpTy .t := !p

/-- Sentence conjunction: p ∧ q -/
def conj {m : Model} (p q : m.interpTy .t) : m.interpTy .t := p && q

/-- Sentence disjunction: p ∨ q -/
def disj {m : Model} (p q : m.interpTy .t) : m.interpTy .t := p || q

/-- Interpret a negated SV sentence: "John doesn't sleep" -/
def interpNegSV (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .t)) : m.interpTy .t :=
  neg (interpSV m subj verb)

/-- Interpret a negated SVO sentence: "John doesn't eat pizza" -/
def interpNegSVO (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (obj : m.interpTy .e) : m.interpTy .t :=
  neg (interpSVO m subj verb obj)

-- Truth Conditions

/-- A sentence is true in a model if its denotation is true -/
def isTrue (m : Model) (meaning : m.interpTy .t) : Prop :=
  meaning = true

-- Examples
example : isTrue toyModel (interpSV toyModel john_sem sleeps_sem) := rfl
example : isTrue toyModel (interpSVO toyModel john_sem eats_sem ToyEntity.pizza) := rfl

-- Negation examples
/-- "Mary doesn't sleep" is true (because Mary doesn't sleep) -/
example : isTrue toyModel (interpNegSV toyModel mary_sem sleeps_sem) := rfl

/-- "John doesn't sleep" is false (because John does sleep) -/
example : interpNegSV toyModel john_sem sleeps_sem = false := rfl

/-- Double negation: neg(neg(p)) = p -/
theorem double_negation {m : Model} (p : m.interpTy .t) : neg (neg p) = p := by
  simp only [neg, Bool.not_not]

-- Counter-examples (these would NOT be provable)
-- example : isTrue toyModel (interpSV toyModel mary_sem sleeps_sem) := rfl  -- would fail

-- Connecting to the SemanticBackend Interface

/-
A model-theoretic semantics provides a SemanticBackend.
The agreement function φ is 1 if true, 0 if false.
(This would require importing SemanticBackend and more setup)
-/

-- Characteristic Functions (Set ↔ Predicate Correspondence)

/-
Following Heim & Kratzer (1998) §1.2.4:

For any set A ⊆ D, there is a unique characteristic function f : D → {0,1}
such that f(x) = 1 iff x ∈ A.

Using Mathlib's `Set`, we can now express this correspondence properly.
-/

/-- Convert a predicate (e → t) to a Set (the extension) -/
def predicateToSet {m : Model} (p : m.interpTy (.e ⇒ .t)) : Set m.Entity :=
  { x | p x = true }

/-- Convert a Set to a predicate (characteristic function) -/
noncomputable def setToPredicate {m : Model} (s : Set m.Entity) [DecidablePred (· ∈ s)]
    : m.interpTy (.e ⇒ .t) :=
  λ x => if x ∈ s then true else false

/-- Check if an entity is in the extension of a predicate -/
def inExtension {m : Model} (p : m.interpTy (.e ⇒ .t)) (x : m.Entity) : Bool := p x

/-- The extension of "sleeps" is {john} -/
theorem sleeps_extension :
    predicateToSet sleeps_sem = {ToyEntity.john} := by
  ext x
  simp only [predicateToSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  cases x <;> simp [sleeps_sem]

/-- The extension of "laughs" is {john, mary} -/
theorem laughs_extension :
    predicateToSet laughs_sem = {ToyEntity.john, ToyEntity.mary} := by
  ext x
  simp only [predicateToSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  cases x <;> simp [laughs_sem]

/-- John is in the extension of "sleeps" -/
theorem john_in_sleeps : inExtension sleeps_sem ToyEntity.john = true := rfl

/-- Mary is not in the extension of "sleeps" -/
theorem mary_not_in_sleeps : inExtension sleeps_sem ToyEntity.mary = false := rfl

/-- Both John and Mary are in the extension of "laughs" -/
theorem john_mary_in_laughs :
    inExtension laughs_sem ToyEntity.john = true ∧
    inExtension laughs_sem ToyEntity.mary = true := ⟨rfl, rfl⟩

-- Schönfinkelization / Currying

/-
Following Heim & Kratzer (1998) §1.3.3:

For any relation R ⊆ D × D, there is a unique curried function f : D → (D → Bool)
such that f(y)(x) = 1 iff (x,y) ∈ R.

In Lean, all functions are already curried. This section makes the correspondence explicit.
-/

/-- Uncurry a binary predicate to a relation on pairs -/
def uncurry {m : Model} (f : m.interpTy (.e ⇒ .e ⇒ .t)) : m.Entity × m.Entity → Bool :=
  λ (x, y) => f y x  -- Note: object first, then subject (linguistic convention)

/-- Curry a relation on pairs to a binary predicate -/
def curry {m : Model} (r : m.Entity × m.Entity → Bool) : m.interpTy (.e ⇒ .e ⇒ .t) :=
  λ y x => r (x, y)

/-- Curry and uncurry are inverses -/
theorem curry_uncurry {m : Model} (f : m.interpTy (.e ⇒ .e ⇒ .t)) :
    curry (uncurry f) = f := rfl

theorem uncurry_curry {m : Model} (r : m.Entity × m.Entity → Bool) :
    uncurry (curry r) = r := rfl

/-- The "sees" relation as a predicate on pairs -/
def seesRelation : ToyEntity × ToyEntity → Bool
  | (ToyEntity.john, ToyEntity.mary) => true
  | (ToyEntity.mary, ToyEntity.john) => true
  | _ => false

/-- uncurry(sees_sem) agrees with seesRelation -/
theorem sees_uncurry_matches :
    ∀ p : ToyEntity × ToyEntity,
      uncurry sees_sem p = seesRelation p := by
  intro ⟨x, y⟩
  cases x <;> cases y <;> rfl

-- Intensional Types (World-Indexed Semantics)

/-!
## Intensional Semantics

For theories involving possible worlds (Chierchia's kinds, Krifka's properties,
modal semantics, etc.), we need world-indexed types.
-/

/-- An intensional property: at each world, a characteristic function on entities -/
abbrev IntensionalProp (Entity World : Type) := World → Entity → Bool

/-- An intensional proposition (sentence meaning) -/
abbrev Proposition (World : Type) := World → Bool

/-- An intensional VP: takes an entity, returns a proposition -/
abbrev IntensionalVP (Entity World : Type) := Entity → Proposition World

/-- Negate a proposition -/
def Proposition.neg {World : Type} (p : Proposition World) : Proposition World :=
  λ w => !p w

/-- Negate a VP (pointwise) -/
def IntensionalVP.neg {Entity World : Type} (vp : IntensionalVP Entity World)
    : IntensionalVP Entity World :=
  λ x w => !vp x w

/-- Existential quantification over a finite domain -/
def IntensionalProp.exists {Entity World : Type}
    (domain : List Entity)
    (prop : IntensionalProp Entity World)
    (vp : IntensionalVP Entity World)
    : Proposition World :=
  λ w => domain.any (λ x => prop w x && vp x w)

end Montague
