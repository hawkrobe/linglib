import Linglib.Core.Logic.Intensional.Frame

/-!
# Toy Domain for Testing

Minimal model for testing compositional semantics:
- `ToyEntity` — four entities (john, mary, pizza, book)
- `toyFrame` — frame over `ToyEntity` with trivial index
- `ToyLexicon` — basic lexical entries (sleeps, sees, eats, reads, etc.)
-/

namespace Semantics.Montague

open Core.Logic.Intensional

inductive ToyEntity where
  | john | mary | pizza | book
  deriving Repr, DecidableEq

def toyFrame : Frame := { Entity := ToyEntity, Index := Unit }

namespace ToyLexicon

open ToyEntity

def john_sem : toyFrame.Denot .e := ToyEntity.john
def mary_sem : toyFrame.Denot .e := ToyEntity.mary

def sleeps_sem : toyFrame.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | _ => False

def laughs_sem : toyFrame.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def sees_sem : toyFrame.Denot (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .mary => True
    | .mary, .john => True
    | _, _ => False

def eats_sem : toyFrame.Denot (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .pizza => True
    | .mary, .pizza => True
    | _, _ => False

def reads_sem : toyFrame.Denot (.e ⇒ .e ⇒ .t) :=
  λ obj => λ subj => match subj, obj with
    | .john, .book => True
    | .mary, .book => True
    | _, _ => False

def pizza_sem : toyFrame.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .pizza => True
    | _ => False

def book_sem : toyFrame.Denot (.e ⇒ .t) :=
  λ x => match x with
    | .book => True
    | _ => False

end ToyLexicon

end Semantics.Montague
