import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

A continuation computation `Cont R A := (A → R) → R` produces its answer
from a continuation `A → R` describing how the result will be used, and
may invoke that continuation any number of times. This file defines
`Cont.lower`, which ends a computation of type `Cont A A` by applying
the identity continuation (Haskell's `evalCont`, not present in
`Mathlib.Control.Monad.Cont`), and proves that `lower` turns a chain of
binds into function application nested in bind order, while the
applicative combination nests in fixed left-to-right order.

In continuation semantics, continuized terms model scope-taking
expressions ([barker-2002]) and `lower` is the LOWER operation of
[barker-shan-2014]; the contrast between free bind order and fixed
applicative order is the monadic account of quantifier scope
([shan-2001], [charlow-2014]). These applications live in
`Composition/Tree.lean` (`PredAbs`), `Studies/BumfordCharlow2024.lean`,
and `Studies/Charlow2020.lean`.

## Main definitions

- `Cont.lower`: evaluation with the identity continuation

## References

- <https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#v:evalCont>
-/

namespace Cont

/-- Evaluation with the identity continuation (functional programming's
`evalCont`, which mathlib does not provide) — [barker-shan-2014]'s LOWER
at `B := A`. Their own LOWER pins the answer type to the atomic clause
category `S`; the pinning carries their crossover account and is not
imposed here. -/
def lower {A : Type*} (m : Cont A A) : A := m.run id

/-- LOWER ∘ LIFT = id: `pure` is [barker-shan-2014]'s LIFT (Montague
lift). -/
@[simp] theorem lower_pure {A : Type*} (a : A) : lower (pure a) = a := rfl

/-! ### `lower` on `pure`/`bind`/`seq` chains

A bind chain lowers to nested application in the order of the binds —
the free reordering read as scope order by [shan-2001]/[charlow-2014] —
while the applicative combination is fixed left-to-right
([barker-shan-2014]'s combination schema and linear scope bias). -/

section LowerChains

universe u

variable {E S : Type u}

/-- `lower` of a bind against a `pure`d function is application. -/
theorem lower_bind_pure (q : Cont S E) (scope : E → S) :
    lower (q >>= λ x => pure (scope x)) = q scope := rfl

/-- `lower` of nested binds is nested application: the outer bind
applies outermost. -/
theorem lower_bind_bind_pure (q₁ q₂ : Cont S E) (rel : E → E → S) :
    lower (q₁ >>= λ x => q₂ >>= λ y => pure (rel x y)) =
    q₁ (λ x => q₂ (λ y => rel x y)) := rfl

/-- The bind-chain pattern at depth three. -/
theorem lower_bind₃_pure (q₁ q₂ q₃ : Cont S E) (rel : E → E → E → S) :
    lower (q₁ >>= λ x => q₂ >>= λ y => q₃ >>= λ z => pure (rel x y z)) =
    q₁ (λ x => q₂ (λ y => q₃ (λ z => rel x y z))) := rfl

/-- `lower` of the applicative combination is nested application in
fixed left-to-right order. -/
theorem lower_map_seq (q₁ q₂ : Cont S E) (rel : E → E → S) :
    lower (rel <$> q₁ <*> q₂) = q₁ (λ x => q₂ (λ y => rel x y)) := rfl

/-- On `pure`-wrapped values, `lower` of a bind chain reduces to
function application ([charlow-2018]). -/
theorem lower_pure_bind_pure {A : Type u} (f : A → S) (x : A) :
    lower ((pure f : Cont S (A → S)) >>= λ g =>
      (pure x : Cont S A) >>= λ y => pure (g y)) = f x := rfl

end LowerChains

end Cont
