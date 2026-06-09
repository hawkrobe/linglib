import Linglib.Core.Logic.Intensional.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Toy English fragment

Minimal pedagogical fragment for compositional-semantics studies:
- `ToyEntity` — four entities (john, mary, pizza, book)
- index type is `Unit` (extensional toy model)
- `ToyLexicon` — basic lexical entries (sleeps, sees, eats, reads, etc.)

Lives in `Fragments/` so substrate files cannot import it — worked examples
over this fragment belong in `Studies/`. The namespace remains
`Semantics.Montague` pending the planned rebuild of this fixture as a
`Semantics.Composition.Model` instance.
-/

namespace Semantics.Montague

open Core.Logic.Intensional

inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq

instance : Fintype ToyEntity where
  elems := {.john, .mary, .pizza, .book}
  complete := fun x => by cases x <;> simp

namespace ToyLexicon

open ToyEntity

def john_sem : Denot ToyEntity Unit .e := ToyEntity.john
def mary_sem : Denot ToyEntity Unit .e := ToyEntity.mary

def sleeps_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | _ => False

def laughs_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def sees_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .mary => True
    | .mary, .john => True
    | _, _ => False

def eats_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .pizza => True
    | .mary, .pizza => True
    | _, _ => False

def reads_sem : Denot ToyEntity Unit (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .book => True
    | .mary, .book => True
    | _, _ => False

def student_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def person_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def thing_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ _ => True

instance : DecidablePred student_sem :=
  fun x => match x with
    | .john | .mary => .isTrue (by simp [student_sem])
    | .pizza | .book => .isFalse (by simp [student_sem])

instance : DecidablePred person_sem :=
  fun x => match x with
    | .john | .mary => .isTrue (by simp [person_sem])
    | .pizza | .book => .isFalse (by simp [person_sem])

instance : DecidablePred thing_sem := fun _ => .isTrue trivial

def pizza_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ x => match x with
    | .pizza => True
    | _ => False

def book_sem : Denot ToyEntity Unit (.e ⇒ .t) :=
  λ x => match x with
    | .book => True
    | _ => False

end ToyLexicon

end Semantics.Montague
