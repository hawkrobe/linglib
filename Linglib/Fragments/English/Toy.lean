import Linglib.Semantics.Composition.Model
import Mathlib.Data.Fintype.Basic

/-!
# Toy English fragment

The pedagogical fragment used by compositional-semantics studies, built the
model-theoretic way: a first-order signature (`toyLang`), a structure carrying
the facts (`toyStructure`), the composition model (`toyModel`), and naming maps
(`toyNaming`) from word forms into the signature. The `ToyLexicon` denotations
are *read off the model* via `Model.const`/`Model.pred₁ext`/`Model.pred₂ext` —
the connection is true by construction, with no bridge theorems.

Lives in `Fragments/` so substrate files cannot import it — worked examples
over this fragment belong in `Studies/`. The namespace remains
`Semantics.Montague` for continuity with the engine's `Lexicon`.
-/

namespace Semantics.Montague

open Core.Logic.Intensional
open FirstOrder
open Semantics.Composition

/-- The four entities. -/
inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq

instance : Fintype ToyEntity where
  elems := {.john, .mary, .pizza, .book}
  complete := fun x => by cases x <;> simp

/-- Unary relation symbols of the toy signature. -/
inductive ToyRel₁ where
  | sleep | laugh | student | person | thing | pizza | book
  deriving Repr, DecidableEq

/-- Binary relation symbols of the toy signature. -/
inductive ToyRel₂ where
  | see | eat | read
  deriving Repr, DecidableEq

/-- The toy lexical signature: every entity is nameable by a constant; content
words are relation symbols. -/
def toyLang : Language where
  Functions := fun n => match n with | 0 => ToyEntity | _ => Empty
  Relations := fun n => match n with | 1 => ToyRel₁ | 2 => ToyRel₂ | _ => Empty

/-- The facts: interpretation of unary symbols. -/
def interpRel₁ : ToyRel₁ → ToyEntity → Prop := fun r x =>
  match r, x with
  | .sleep, .john => True
  | .sleep, _ => False
  | .laugh, .john => True
  | .laugh, .mary => True
  | .laugh, _ => False
  | .student, .john => True
  | .student, .mary => True
  | .student, _ => False
  | .person, .john => True
  | .person, .mary => True
  | .person, _ => False
  | .thing, _ => True
  | .pizza, .pizza => True
  | .pizza, _ => False
  | .book, .book => True
  | .book, _ => False

/-- The facts: interpretation of binary symbols (subject-first). -/
def interpRel₂ : ToyRel₂ → ToyEntity → ToyEntity → Prop := fun r subj obj =>
  match r, subj, obj with
  | .see, .john, .mary => True
  | .see, .mary, .john => True
  | .see, _, _ => False
  | .eat, .john, .pizza => True
  | .eat, .mary, .pizza => True
  | .eat, _, _ => False
  | .read, .john, .book => True
  | .read, .mary, .book => True
  | .read, _, _ => False

/-- The toy structure: constants denote themselves; relations carry the facts. -/
def toyStructure : toyLang.Structure ToyEntity where
  funMap {n} f v :=
    match n, f, v with
    | 0, c, _ => c
    | _ + 1, f, _ => nomatch f
  RelMap {n} r v :=
    match n, r, v with
    | 0, r, _ => nomatch r
    | 1, r, v => interpRel₁ r (v 0)
    | 2, r, v => interpRel₂ r (v 0) (v 1)
    | _ + 3, r, _ => nomatch r

/-- The toy composition model: extensional (one world). -/
def toyModel : Model toyLang where
  E := ToyEntity
  W := Unit
  interp _ := toyStructure

/-- The naming maps: word forms into the toy signature. -/
def toyNaming : LexNaming toyLang where
  names := fun s =>
    match s with
    | "John" => some ToyEntity.john
    | "Mary" => some ToyEntity.mary
    | _ => none
  preds₁ := fun s =>
    match s with
    | "sleeps" => some ToyRel₁.sleep
    | "laughs" => some ToyRel₁.laugh
    | "student" => some ToyRel₁.student
    | "person" => some ToyRel₁.person
    | "thing" => some ToyRel₁.thing
    | "pizza" => some ToyRel₁.pizza
    | "book" => some ToyRel₁.book
    | _ => none
  preds₂ := fun s =>
    match s with
    | "sees" => some ToyRel₂.see
    | "eats" => some ToyRel₂.eat
    | "reads" => some ToyRel₂.read
    | _ => none

/-- The toy lexicon, induced by the naming maps over the model. -/
def toyLexicon : Lexicon ToyEntity Unit := toyModel.lexiconAt toyNaming ()

namespace ToyLexicon

/-! Denotations read off the model. Each is definitionally the corresponding
match-function over `ToyEntity`, so `rfl`/`trivial` proofs over them reduce. -/

def john_sem : Denot ToyEntity Unit .e := toyModel.const ToyEntity.john ()
def mary_sem : Denot ToyEntity Unit .e := toyModel.const ToyEntity.mary ()

def sleeps_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.sleep ()
def laughs_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.laugh ()
def student_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.student ()
def person_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.person ()
def thing_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.thing ()
def pizza_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.pizza ()
def book_sem : Denot ToyEntity Unit (.e ⇒ .t) := toyModel.pred₁ext ToyRel₁.book ()

def sees_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext ToyRel₂.see ()
def eats_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext ToyRel₂.eat ()
def reads_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) := toyModel.pred₂ext ToyRel₂.read ()

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
