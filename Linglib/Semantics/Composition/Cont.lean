import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

`Cont.lower` evaluates a computation `Cont A A` at the identity
continuation — Haskell's `evalCont`, which `Mathlib.Control.Monad.Cont`
does not provide. The `lower_pure`/`lower_bind`/`lower_map`/`lower_seq`
simp set mirrors `ContT`'s `run_*` lemmas; under it, bind chains
evaluate in bind order and the applicative combination left-to-right.
In continuation semantics `lower` is [barker-shan-2014]'s LOWER (theirs
restricts the answer type to the clause category), and the bind-order
dependence is the monadic account of quantifier scope ([barker-2002],
[shan-2001], [charlow-2014]); see `Studies/BumfordCharlow2024.lean` and
`Studies/Charlow2020.lean`.

## References

- <https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#v:evalCont>
-/

universe u

namespace Cont

variable {α β : Type u}

/-- Evaluation at the identity continuation: `lower m = m id`. -/
def lower (m : Cont α α) : α := m.run id

/-! ### Interaction with the monad operations -/

/-- `lower` is a left inverse of `pure`: LOWER ∘ LIFT is the identity. -/
@[simp] theorem lower_pure (a : α) : lower (pure a) = a := rfl

@[simp] theorem lower_bind (m : Cont β α) (f : α → Cont β β) :
    lower (m >>= f) = m.run λ x => lower (f x) := rfl

@[simp] theorem lower_map (f : α → β) (m : Cont β α) :
    lower (f <$> m) = m.run f := rfl

@[simp] theorem lower_seq (mf : Cont β (α → β)) (mx : Cont β α) :
    lower (mf <*> mx) = mf.run λ f => mx.run f := rfl

end Cont
