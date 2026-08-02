import Mathlib.Control.Monad.Cont

/-!
# Continuations for scope-taking
[barker-2002] [shan-2001] [charlow-2014] [barker-shan-2014]

Scope-taking expressions denote values of the continuation monad
`Cont R A := (A → R) → R` (`Mathlib.Control.Monad.Cont`): continuations for
quantifier scope originate with [barker-2002]; the monadic framing is
[shan-2001], developed by [charlow-2014]. Consumers: higher-order dynamic
GQs (`Studies/Charlow2021.lean`) and the effects fragment of
`Studies/BumfordCharlow2024.lean`.

## Main definitions

- `Cont.lower`: evaluate with the identity continuation — "scope-taking is
  done". `pure` is Montague lift ([barker-shan-2014]'s LIFT), and
  `Cont.lower_pure` is LOWER ∘ LIFT = id.

## Main statements

- `Cont.lower_bind_pure` and variants: lowering a chain of binds is nested
  generalized-quantifier application — relative scope is bind order.
-/

namespace Semantics.Composition.Continuation

/-- LOWER: evaluate with the identity continuation — [barker-shan-2014]'s
"scope-taking is done", at `B := A`. Their own LOWER pins the answer type to
the atomic clause category `S`; the pinning carries their crossover account
and is not imposed here. -/
def Cont.lower {A : Type*} (m : Cont A A) : A := m.run id

/-- LOWER ∘ LIFT = id: `pure : A → Cont R A` is [barker-shan-2014]'s LIFT
(Montague lift), and lowering it recovers the value. -/
@[simp] theorem Cont.lower_pure {A : Type*} (a : A) :
    Cont.lower (pure a) = a := rfl

/-! ### Scope as bind order

In the monadic framing, relative quantifier scope is the *order of monadic
bind* — surface scope binds the subject first, inverse scope the object
first — and `Cont.lower` is generalized-quantifier application
([shan-2001], [charlow-2014]). Free bind order contrasts with
[barker-shan-2014]'s combination schema, whose fixed left-to-right
evaluation (their linear scope bias) derives inverse scope from multi-level
towers instead. -/

section ScopeAsBindOrder

universe u

variable {E S : Type u}

/-- Lowering a continuized quantifier against a pure scope is plain GQ
application. -/
theorem Cont.lower_bind_pure (q : Cont S E) (scope : E → S) :
    Cont.lower (q >>= λ x => pure (scope x)) = q scope := rfl

/-- Nested binds compute nested GQ application: the outer bind takes wide
scope. -/
theorem Cont.lower_bind_bind_pure (q₁ q₂ : Cont S E) (rel : E → E → S) :
    Cont.lower (q₁ >>= λ x => q₂ >>= λ y => pure (rel x y)) =
    q₁ (λ x => q₂ (λ y => rel x y)) := rfl

/-- The bind-order pattern extends to arbitrary depth. -/
theorem Cont.lower_bind₃_pure (q₁ q₂ q₃ : Cont S E) (rel : E → E → E → S) :
    Cont.lower (q₁ >>= λ x => q₂ >>= λ y => q₃ >>= λ z => pure (rel x y z)) =
    q₁ (λ x => q₂ (λ y => q₃ (λ z => rel x y z))) := rfl

/-- When every meaning is `pure`-wrapped, `Cont` composition reduces to
function application: the effect-free fragment embeds into `Cont`
([charlow-2018]). -/
theorem Cont.lower_pure_bind_pure {A : Type u} (f : A → S) (x : A) :
    Cont.lower ((pure f : Cont S (A → S)) >>= λ g =>
      (pure x : Cont S A) >>= λ y => pure (g y)) = f x := rfl

end ScopeAsBindOrder

end Semantics.Composition.Continuation
