import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

A value of `Cont R A := (A → R) → R` (`Mathlib.Control.Monad.Cont`) is a
computation handed its own future: given a continuation `A → R` saying
how the rest of the derivation will use its result, it produces the
final answer — and may consult that continuation zero, one, or many
times. `Cont.lower` ends the computation: once the answer type equals
the value type, applying the identity continuation extracts the result.
`pure` is the converse embedding — a value wrapped so that any
continuation applies to it directly — and lowering undoes it
(`Cont.lower_pure`).

What `lower` returns on composite computations is the substance of this
file: a chain of binds lowers to nested application, nested in exactly
the order of the binds, while the applicative combination `<$> … <*>`
always nests left over right. That contrast carries the linguistic
reading: continuized values model scope-taking expressions
([barker-2002]), `lower` is [barker-shan-2014]'s LOWER ("scope-taking
is done"), and free bind order — read as free quantifier scope by
[shan-2001] and [charlow-2014] — is exactly what the order-fixed
applicative fragment withholds. The applications live with the
composition engine (`PredAbs` in `Composition/Tree.lean`) and its
studies (`Studies/BumfordCharlow2024.lean`, `Studies/Charlow2020.lean`).

## Main definitions

- `Cont.lower`: evaluation with the identity continuation
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
