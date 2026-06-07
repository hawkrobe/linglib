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

/-! ### Scope as bind order

Scope ambiguity in the continuation framework is the *order of monadic
bind* — surface scope binds the subject first, inverse scope the object
first — and `lower` is generalized-quantifier application
([barker-shan-2014]). These hold for any quantifier and predicate. -/

section ScopeAsBindOrder

variable {E S : Type}

/-- Lowering a `Cont`-wrapped quantifier with a pure scope predicate is
plain GQ application: `lower (Q >>= λx. pure (P x)) = Q P`. -/
theorem cont_scope_reduce (q : Cont S E) (scope : E → S) :
    Cont.lower (Cont.bind q (fun x => Cont.pure (scope x))) = q scope := rfl

/-- Nested `Cont` binds compute nested GQ application; the bind nesting
determines scope order. -/
theorem cont_scope_double (q₁ q₂ : Cont S E) (rel : E → E → S) :
    Cont.lower (Cont.bind q₁ (fun x =>
      Cont.bind q₂ (fun y => Cont.pure (rel x y)))) =
    q₁ (fun x => q₂ (fun y => rel x y)) := rfl

/-- **Scope ambiguity = bind order**: the two readings of `Q₁ R Q₂` are
`Q₁` nested outside `Q₂` vs `Q₂` outside `Q₁`, each reducing to GQ
application in the corresponding order. -/
theorem scope_ambiguity_is_bind_order (q₁ q₂ : Cont S E) (rel : E → E → S) :
    Cont.lower (Cont.bind q₁ (fun x =>
      Cont.bind q₂ (fun y => Cont.pure (rel x y)))) =
    q₁ (fun x => q₂ (fun y => rel x y))
    ∧
    Cont.lower (Cont.bind q₂ (fun y =>
      Cont.bind q₁ (fun x => Cont.pure (rel x y)))) =
    q₂ (fun y => q₁ (fun x => rel x y)) :=
  ⟨rfl, rfl⟩

/-- The bind-order pattern extends to arbitrary depth. -/
theorem cont_scope_triple (q₁ q₂ q₃ : Cont S E) (rel : E → E → E → S) :
    Cont.lower (Cont.bind q₁ (fun x =>
      Cont.bind q₂ (fun y =>
        Cont.bind q₃ (fun z => Cont.pure (rel x y z))))) =
    q₁ (fun x => q₂ (fun y => q₃ (fun z => rel x y z))) := rfl

/-- When all meanings are `Cont.pure`-wrapped, `Cont` composition reduces
to function application — the non-scope-taking (Reader) fragment embeds
into `Cont` ([charlow-2018]). -/
theorem cont_pure_is_fa {A : Type} (f : A → S) (x : A) :
    Cont.lower (Cont.bind (Cont.pure f) (fun g =>
      Cont.bind (Cont.pure x) (fun y => Cont.pure (g y)))) = f x := rfl

end ScopeAsBindOrder

end Semantics.Composition.Continuation
