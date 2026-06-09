import Linglib.Core.Logic.Intensional.Frame

/-!
# Toy Domain for Testing

Minimal model for testing compositional semantics:
- `ToyEntity` — four entities (john, mary, pizza, book)
- index type is `Unit` (extensional toy model)
- `ToyLexicon` — basic lexical entries (sleeps, sees, eats, reads, etc.)
-/

namespace Semantics.Montague

open Core.Logic.Intensional

inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq

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
