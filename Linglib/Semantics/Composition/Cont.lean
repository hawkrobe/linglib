import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

`Cont.lower` evaluates a computation `Cont A A` at the identity
continuation — Haskell's `evalCont`, which `Mathlib.Control.Monad.Cont`
does not provide. The lemmas compute `lower` over `pure`/`>>=`/`<*>`
chains: binds nest in bind order, the applicative combination
left-to-right. In continuation semantics `lower` is
[barker-shan-2014]'s LOWER (theirs restricts the answer type to the
clause category), and the bind-order dependence is the
monadic account of quantifier scope ([barker-2002], [shan-2001],
[charlow-2014]); see `Studies/BumfordCharlow2024.lean` and
`Studies/Charlow2020.lean`.

## References

- <https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#v:evalCont>
-/

namespace Cont

/-- Evaluation at the identity continuation: `lower m = m id`. -/
def lower {A : Type*} (m : Cont A A) : A := m.run id

/-- `lower` is a left inverse of `pure`: LOWER ∘ LIFT is the identity. -/
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
