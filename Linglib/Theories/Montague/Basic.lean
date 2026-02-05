/-
# Montague-Style Compositional Semantics

## Semantic Types

- `e` : entities
- `t` : truth values
- `e → t` : properties
- `e → e → t` : relations
- `(e → t) → t` : generalized quantifiers

## Composition

Function application: if α has type σ → τ and β has type σ, then ⟦α β⟧ = ⟦α⟧(⟦β⟧).
-/

import Linglib.Core.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

namespace Montague

/-- Semantic types (Montague's type theory). -/
inductive Ty where
  | e    -- entities
  | t    -- truth values
  | s    -- possible worlds
  | fn : Ty → Ty → Ty
  deriving Repr, DecidableEq

infixr:25 " ⇒ " => Ty.fn

def Ty.et : Ty := .e ⇒ .t
def Ty.eet : Ty := .e ⇒ .e ⇒ .t
def Ty.ett : Ty := (.e ⇒ .t) ⇒ .t
def Ty.st : Ty := .s ⇒ .t
def Ty.se : Ty := .s ⇒ .e

structure Model where
  Entity : Type
  World : Type := Unit
  decEq : DecidableEq Entity

/-- Interpretation of types in a model. -/
def Model.interpTy (m : Model) : Ty → Type
  | .e => m.Entity
  | .t => Bool
  | .s => m.World
  | .fn σ τ => m.interpTy σ → m.interpTy τ

inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq

def toyModel : Model := { Entity := ToyEntity, decEq := inferInstance }

structure LexEntry (m : Model) where
  ty : Ty
  denot : m.interpTy ty

def Lexicon (m : Model) := String → Option (LexEntry m)

namespace ToyLexicon

open ToyEntity

def john_sem : toyModel.interpTy .e := ToyEntity.john
def mary_sem : toyModel.interpTy .e := ToyEntity.mary

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

def pizza_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .pizza => true
    | _ => false

def book_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .book => true
    | _ => false

end ToyLexicon

section Composition

def apply {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) : m.interpTy τ :=
  f x

structure SemanticDeriv (m : Model) where
  words : List Word
  ty : Ty
  meaning : m.interpTy ty

def interpSV (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .t)) : m.interpTy .t :=
  apply verb subj

def interpSVO (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (obj : m.interpTy .e) : m.interpTy .t :=
  apply (apply verb obj) subj

end Composition

section SententialOperators

/-- Sentence negation. See `Core.Proposition.Decidable.pnot` for the
world-indexed version with proven DE property. -/
def neg {m : Model} (p : m.interpTy .t) : m.interpTy .t := !p

def conj {m : Model} (p q : m.interpTy .t) : m.interpTy .t := p && q
def disj {m : Model} (p q : m.interpTy .t) : m.interpTy .t := p || q

def interpNegSV (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .t)) : m.interpTy .t :=
  neg (interpSV m subj verb)

def interpNegSVO (m : Model)
    (subj : m.interpTy .e)
    (verb : m.interpTy (.e ⇒ .e ⇒ .t))
    (obj : m.interpTy .e) : m.interpTy .t :=
  neg (interpSVO m subj verb obj)

end SententialOperators

open ToyLexicon

section TruthConditions

def isTrue (m : Model) (meaning : m.interpTy .t) : Prop :=
  meaning = true

example : isTrue toyModel (interpSV toyModel john_sem sleeps_sem) := rfl
example : isTrue toyModel (interpSVO toyModel john_sem eats_sem ToyEntity.pizza) := rfl
example : isTrue toyModel (interpNegSV toyModel mary_sem sleeps_sem) := rfl
example : interpNegSV toyModel john_sem sleeps_sem = false := rfl

theorem double_negation {m : Model} (p : m.interpTy .t) : neg (neg p) = p := by
  simp only [neg, Bool.not_not]

end TruthConditions

section CharacteristicFunctions

/-- Convert a predicate `e → t` to a `Set` (the extension). -/
def predicateToSet {m : Model} (p : m.interpTy (.e ⇒ .t)) : Set m.Entity :=
  { x | p x = true }

noncomputable def setToPredicate {m : Model} (s : Set m.Entity) [DecidablePred (· ∈ s)]
    : m.interpTy (.e ⇒ .t) :=
  λ x => if x ∈ s then true else false

def inExtension {m : Model} (p : m.interpTy (.e ⇒ .t)) (x : m.Entity) : Bool := p x

theorem sleeps_extension :
    predicateToSet sleeps_sem = {ToyEntity.john} := by
  ext x
  simp only [predicateToSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  cases x <;> simp [sleeps_sem]

theorem laughs_extension :
    predicateToSet laughs_sem = {ToyEntity.john, ToyEntity.mary} := by
  ext x
  simp only [predicateToSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  cases x <;> simp [laughs_sem]

theorem john_in_sleeps : inExtension sleeps_sem ToyEntity.john = true := rfl
theorem mary_not_in_sleeps : inExtension sleeps_sem ToyEntity.mary = false := rfl
theorem john_mary_in_laughs :
    inExtension laughs_sem ToyEntity.john = true ∧
    inExtension laughs_sem ToyEntity.mary = true := ⟨rfl, rfl⟩

end CharacteristicFunctions

section Currying

def uncurry {m : Model} (f : m.interpTy (.e ⇒ .e ⇒ .t)) : m.Entity × m.Entity → Bool :=
  λ (x, y) => f y x

def curry {m : Model} (r : m.Entity × m.Entity → Bool) : m.interpTy (.e ⇒ .e ⇒ .t) :=
  λ y x => r (x, y)

theorem curry_uncurry {m : Model} (f : m.interpTy (.e ⇒ .e ⇒ .t)) :
    curry (uncurry f) = f := rfl

theorem uncurry_curry {m : Model} (r : m.Entity × m.Entity → Bool) :
    uncurry (curry r) = r := rfl

def seesRelation : ToyEntity × ToyEntity → Bool
  | (ToyEntity.john, ToyEntity.mary) => true
  | (ToyEntity.mary, ToyEntity.john) => true
  | _ => false

theorem sees_uncurry_matches :
    ∀ p : ToyEntity × ToyEntity,
      uncurry sees_sem p = seesRelation p := by
  intro ⟨x, y⟩
  cases x <;> cases y <;> rfl

end Currying

section IntensionalTypes

/-!
## Intensional Semantics

World-indexed types for modal semantics, kind reference, etc.
-/

abbrev IntensionalProp (Entity World : Type) := World → Entity → Bool
abbrev Proposition (World : Type) := World → Bool
abbrev IntensionalVP (Entity World : Type) := Entity → Proposition World

def Proposition.neg {World : Type} (p : Proposition World) : Proposition World :=
  λ w => !p w

def IntensionalVP.neg {Entity World : Type} (vp : IntensionalVP Entity World)
    : IntensionalVP Entity World :=
  λ x w => !vp x w

def IntensionalProp.exists {Entity World : Type}
    (domain : List Entity)
    (prop : IntensionalProp Entity World)
    (vp : IntensionalVP Entity World)
    : Proposition World :=
  λ w => domain.any (λ x => prop w x && vp x w)

end IntensionalTypes

end Montague
