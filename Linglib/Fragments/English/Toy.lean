import Linglib.Semantics.Composition.Model
import Linglib.Semantics.Composition.Reduction
import Mathlib.Data.Fintype.Basic

/-!
# Toy English fragment

The pedagogical fragment used by compositional-semantics studies, built the
model-theoretic way and in mathlib's concrete-language idiom (after
`Mathlib/ModelTheory/Algebra/Ring/Basic.lean`): arity-indexed symbol inductives
(`toyFunc`, `toyRel`), the signature (`toyLang`), per-symbol defeq abbreviations
(`sleepRel`, …), a structure carrying the facts (`toyStructure`) with one
`@[simp]` lemma per symbol, the composition model (`toyModel`), and naming maps
(`toyNaming`) from word forms into the signature. The `ToyLexicon` denotations
are *read off the model* via `Model.const`/`Model.pred₁ext`/`Model.pred₂ext` —
the connection is true by construction, with no bridge theorems.

Lives in `Fragments/` so substrate files cannot import it — worked examples
over this fragment belong in `Studies/`. The namespace remains
`Semantics.Montague` for continuity with the engine's `Lexicon`.
-/

namespace Semantics.Montague

open Intensional
open FirstOrder
open Semantics.Composition

/-- The four entities. -/
inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq

instance : Fintype ToyEntity where
  elems := {.john, .mary, .pizza, .book}
  complete := fun x => by cases x <;> simp

/-- Function symbols of the toy signature: constants naming entities. -/
inductive toyFunc : ℕ → Type
  | john : toyFunc 0
  | mary : toyFunc 0
  deriving DecidableEq

/-- Relation symbols of the toy signature: content words at their arities. -/
inductive toyRel : ℕ → Type
  | sleep : toyRel 1
  | laugh : toyRel 1
  | student : toyRel 1
  | person : toyRel 1
  | thing : toyRel 1
  | pizza : toyRel 1
  | book : toyRel 1
  | see : toyRel 2
  | eat : toyRel 2
  | read : toyRel 2
  deriving DecidableEq

/-- The toy lexical signature. -/
def toyLang : Language :=
  { Functions := toyFunc
    Relations := toyRel }

/-! Per-symbol abbreviations with the defeq types `toyLang.Constants` /
`toyLang.Relations n` (mathlib's `addFunc` idiom), so symbols elaborate
without unfolding `toyLang`. -/

abbrev johnConst : toyLang.Constants := .john
abbrev maryConst : toyLang.Constants := .mary
abbrev sleepRel : toyLang.Relations 1 := .sleep
abbrev laughRel : toyLang.Relations 1 := .laugh
abbrev studentRel : toyLang.Relations 1 := .student
abbrev personRel : toyLang.Relations 1 := .person
abbrev thingRel : toyLang.Relations 1 := .thing
abbrev pizzaRel : toyLang.Relations 1 := .pizza
abbrev bookRel : toyLang.Relations 1 := .book
abbrev seeRel : toyLang.Relations 2 := .see
abbrev eatRel : toyLang.Relations 2 := .eat
abbrev readRel : toyLang.Relations 2 := .read

/-! ### The facts -/

namespace ToyFacts

def sleep : ToyEntity → Prop := fun x =>
  match x with
  | .john => True
  | _ => False

def laugh : ToyEntity → Prop := fun x =>
  match x with
  | .john => True
  | .mary => True
  | _ => False

def student : ToyEntity → Prop := fun x =>
  match x with
  | .john => True
  | .mary => True
  | _ => False

def person : ToyEntity → Prop := fun x =>
  match x with
  | .john => True
  | .mary => True
  | _ => False

def thing : ToyEntity → Prop := fun _ => True

def pizza : ToyEntity → Prop := fun x =>
  match x with
  | .pizza => True
  | _ => False

def book : ToyEntity → Prop := fun x =>
  match x with
  | .book => True
  | _ => False

def see : ToyEntity → ToyEntity → Prop := fun subj obj =>
  match subj, obj with
  | .john, .mary => True
  | .mary, .john => True
  | _, _ => False

def eat : ToyEntity → ToyEntity → Prop := fun subj obj =>
  match subj, obj with
  | .john, .pizza => True
  | .mary, .pizza => True
  | _, _ => False

def read : ToyEntity → ToyEntity → Prop := fun subj obj =>
  match subj, obj with
  | .john, .book => True
  | .mary, .book => True
  | _, _ => False

end ToyFacts

/-- The toy structure: constants denote their entities; relations carry the
facts (binary relations subject-first). -/
def toyStructure : toyLang.Structure ToyEntity where
  funMap {n} f v :=
    match f, v with
    | .john, _ => ToyEntity.john
    | .mary, _ => ToyEntity.mary
  RelMap {n} r v :=
    match r, v with
    | .sleep, v => ToyFacts.sleep (v 0)
    | .laugh, v => ToyFacts.laugh (v 0)
    | .student, v => ToyFacts.student (v 0)
    | .person, v => ToyFacts.person (v 0)
    | .thing, v => ToyFacts.thing (v 0)
    | .pizza, v => ToyFacts.pizza (v 0)
    | .book, v => ToyFacts.book (v 0)
    | .see, v => ToyFacts.see (v 0) (v 1)
    | .eat, v => ToyFacts.eat (v 0) (v 1)
    | .read, v => ToyFacts.read (v 0) (v 1)

/-! One `@[simp]` lemma per symbol (mathlib's `funMap_add` discipline), so
proofs reduce `RelMap`/`funMap` to the named facts without unfolding the
structure. -/

@[simp] theorem funMap_john (v : Fin 0 → ToyEntity) :
    toyStructure.funMap johnConst v = ToyEntity.john := rfl
@[simp] theorem funMap_mary (v : Fin 0 → ToyEntity) :
    toyStructure.funMap maryConst v = ToyEntity.mary := rfl
@[simp] theorem relMap_sleep (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap sleepRel v = ToyFacts.sleep (v 0) := rfl
@[simp] theorem relMap_laugh (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap laughRel v = ToyFacts.laugh (v 0) := rfl
@[simp] theorem relMap_student (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap studentRel v = ToyFacts.student (v 0) := rfl
@[simp] theorem relMap_person (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap personRel v = ToyFacts.person (v 0) := rfl
@[simp] theorem relMap_thing (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap thingRel v = ToyFacts.thing (v 0) := rfl
@[simp] theorem relMap_pizza (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap pizzaRel v = ToyFacts.pizza (v 0) := rfl
@[simp] theorem relMap_book (v : Fin 1 → ToyEntity) :
    toyStructure.RelMap bookRel v = ToyFacts.book (v 0) := rfl
@[simp] theorem relMap_see (v : Fin 2 → ToyEntity) :
    toyStructure.RelMap seeRel v = ToyFacts.see (v 0) (v 1) := rfl
@[simp] theorem relMap_eat (v : Fin 2 → ToyEntity) :
    toyStructure.RelMap eatRel v = ToyFacts.eat (v 0) (v 1) := rfl
@[simp] theorem relMap_read (v : Fin 2 → ToyEntity) :
    toyStructure.RelMap readRel v = ToyFacts.read (v 0) (v 1) := rfl

/-- The toy composition model: extensional (one world). -/
def toyModel : Model toyLang where
  E := ToyEntity
  W := Unit
  interp _ := toyStructure

/-- The naming maps: word forms into the toy signature. -/
def toyNaming : LexNaming toyLang where
  names := fun s =>
    match s with
    | "John" => some johnConst
    | "Mary" => some maryConst
    | _ => none
  preds₁ := fun s =>
    match s with
    | "sleeps" => some sleepRel
    | "laughs" => some laughRel
    | "student" => some studentRel
    | "person" => some personRel
    | "thing" => some thingRel
    | "pizza" => some pizzaRel
    | "book" => some bookRel
    | _ => none
  preds₂ := fun s =>
    match s with
    | "sees" => some seeRel
    | "eats" => some eatRel
    | "reads" => some readRel
    | _ => none

/-- The toy lexicon, induced by the naming maps over the model. -/
def toyLexicon : Lexicon ToyEntity Unit := toyModel.lexiconAt toyNaming ()

/-- The toy naming maps classify each word once. -/
theorem toyNaming_disjoint : toyNaming.Disjoint := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro s R h
      simp only [toyNaming] at h ⊢
      split at h <;> simp_all

/-- The default logical vocabulary is fresh for the toy naming maps. -/
theorem toyNaming_freshFor : FOWords.FreshFor {} toyNaming := by
  intro s hs
  fin_cases hs <;> exact ⟨rfl, rfl, rfl⟩

namespace ToyLexicon

/-! Denotations read off the model. Each is definitionally the corresponding
fact predicate over `ToyEntity`, so `rfl`/`trivial` proofs over them reduce. -/

def john_sem : Denot ToyEntity Unit .e := toyModel.const johnConst ()
def mary_sem : Denot ToyEntity Unit .e := toyModel.const maryConst ()

def sleeps_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext sleepRel ()
def laughs_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext laughRel ()
def student_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext studentRel ()
def person_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext personRel ()
def thing_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext thingRel ()
def pizza_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext pizzaRel ()
def book_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext bookRel ()

def sees_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext seeRel ()
def eats_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext eatRel ()
def reads_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext readRel ()

instance : DecidablePred student_sem := fun x =>
  match x with
  | .john | .mary => .isTrue trivial
  | .pizza | .book => .isFalse id

instance : DecidablePred person_sem := fun x =>
  match x with
  | .john | .mary => .isTrue trivial
  | .pizza | .book => .isFalse id

instance : DecidablePred thing_sem := fun _ => .isTrue trivial

end ToyLexicon

/-- Engine smoke test: "John sleeps" composes (via the real `Tree.interp`, over the
naming-map-induced lexicon) to the model's fact. -/
example :
    Tree.interp ToyEntity Unit toyLexicon (fun _ => ToyEntity.john)
      (.node () [.terminal () "John", .terminal () "sleeps"] : Syntax.Tree Unit String)
      = some ⟨.t, ToyLexicon.sleeps_sem ToyLexicon.john_sem⟩ := rfl

end Semantics.Montague
