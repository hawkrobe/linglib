import Mathlib.Tactic.Basic

/-!
# Continuation Monad

General-purpose continuation monad, following Barker & Shan (2014).
The type `Cont R A := (A → R) → R` underlies lifted question types
(LiftedTypes.lean), higher-order dynamic GQs (Charlow 2021), and
scope-taking expressions generally.

## Key definitions

- `Cont R A`: the continuation monad
- `Cont.pure`, `Cont.bind`, `Cont.map`: monad operations
- `Cont.lower`: Barker & Shan's LOWER (evaluate with identity continuation)
- `Tower C B A`: Barker & Shan's tower abbreviation `(A → B) → C`

## References

- Barker, C. & Shan, C. (2014). *Continuations and Natural Language*. OUP.
- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
-/

namespace Core.Continuation

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

-- ════════════════════════════════════════════════════
-- § Monad Laws
-- ════════════════════════════════════════════════════

/-- Left identity: `pure a >>= f = f a` -/
theorem Cont.bind_left_id (a : A) (f : A → Cont R B) :
    Cont.bind (Cont.pure a) f = f a := rfl

/-- Right identity: `m >>= pure = m` -/
theorem Cont.bind_right_id (m : Cont R A) :
    Cont.bind m Cont.pure = m := rfl

/-- Associativity: `(m >>= f) >>= g = m >>= (λa. f a >>= g)` -/
theorem Cont.bind_assoc {C : Type*} (m : Cont R A) (f : A → Cont R B)
    (g : B → Cont R C) :
    Cont.bind (Cont.bind m f) g = Cont.bind m (λ a => Cont.bind (f a) g) := rfl

/-- Map can be defined via bind and pure. -/
theorem Cont.map_via_bind (f : A → B) (m : Cont R A) :
    Cont.map f m = Cont.bind m (λ a => Cont.pure (f a)) := rfl

/-- Lower of pure is identity. -/
theorem Cont.lower_pure (a : A) : Cont.lower (Cont.pure a) = a := rfl

end Core.Continuation
