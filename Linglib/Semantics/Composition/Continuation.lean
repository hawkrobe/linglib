import Mathlib.Tactic.Basic

/-!
# Continuation Monad
[barker-shan-2014] [charlow-2021]

General-purpose continuation monad, following [barker-shan-2014].
The type `Cont R A := (A → R) → R` underlies lifted question types
(Lifted.lean), higher-order dynamic GQs, and
scope-taking expressions generally.

## Key definitions

- `Cont R A`: the continuation monad
- `Cont.pure`, `Cont.bind`, `Cont.map`: monad operations
- `Cont.lower`: Barker & Shan's LOWER (evaluate with identity continuation)
- `Tower C B A`: Barker & Shan's tower abbreviation `(A → B) → C`

-/

namespace Semantics.Composition.Continuation

universe u v w

/-- The continuation monad: `(A → R) → R`.
    An expression of type `Cont R A` takes a continuation `A → R` and
    produces a result of type `R`. -/
def Cont (R : Type u) (A : Type v) := (A → R) → R

variable {R : Type u} {A : Type v} {B : Type w}

/-- Monadic unit: wrap a value for any continuation.
    `pure a = λκ. κ(a)` -/
def Cont.pure (a : A) : Cont R A := λ κ => κ a

/-- Monadic bind: sequence two continuized computations.
    `m >>= f = λκ. m(λa. f(a)(κ))` -/
def Cont.bind (m : Cont R A) (f : A → Cont R B) : Cont R B :=
  λ κ => m (λ a => f a κ)

/-- Functorial map: apply a function under the continuation.
    `map f m = λκ. m(λa. κ(f(a)))` -/
def Cont.map (f : A → B) (m : Cont R A) : Cont R B :=
  λ κ => m (λ a => κ (f a))

/-- LOWER: evaluate a `Cont A A` with the identity continuation.
    Barker & Shan's key operation for "scope-taking is done." -/
def Cont.lower (m : Cont A A) : A := m id

/-- Tower type abbreviation: `(A → B) → C`.
    In Barker & Shan's notation, this is the flat reading of
    ```
      C | B
      ─────
        A
    ``` -/
abbrev Tower (C : Type u) (B : Type v) (A : Type w) := (A → B) → C


/-! The continuation monad's laws (left/right identity, associativity, and the
functor laws) are exactly those of `LawfulMonad`, so we register `Cont R` as a
lawful monad rather than restating them as standalone `rfl` theorems. `R` is
fixed to `Type` (not universe-polymorphic) for Lean's `Monad` class. -/

section Instances

variable {R : Type}

instance : Functor (Cont R) where
  map := Cont.map

instance : Pure (Cont R) where
  pure := Cont.pure

instance : Bind (Cont R) where
  bind := Cont.bind

instance : Seq (Cont R) where
  seq mf mx := Cont.bind mf (λ f => Cont.map f (mx ()))

instance : Monad (Cont R) where

instance : LawfulMonad (Cont R) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
  bind_pure_comp _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl
  bind_map _ _ := rfl
  pure_seq _ _ := rfl
  seq_pure _ _ := rfl
  seq_assoc _ _ _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  map_pure _ _ := rfl

end Instances

/-- Lower of pure is identity. (Not a monad law — a fact about `Cont.lower`.) -/
theorem Cont.lower_pure (a : A) : Cont.lower (Cont.pure a) = a := rfl

end Semantics.Composition.Continuation
