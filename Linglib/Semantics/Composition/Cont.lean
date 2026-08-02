import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

`ContT.lower` finishes a continuation computation by handing it the
trivial continuation `pure` — [charlow-2014]'s Lowering, Haskell's
`evalCont`, the LOWER of [barker-shan-2014]. The `lower_*` simp lemmas
mirror `ContT`'s `run_*` set: a chain of binds evaluates in bind order
and the applicative combination left-to-right, which is what lets bind
order model quantifier scope. `ContT.reset` lowers and then re-lifts,
delimiting scope the way scope islands do. For the linguistic
applications see `Studies/BumfordCharlow2024.lean` and
`Studies/Charlow2020.lean`.

## References

- <https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#v:evalCont>
-/

universe u v

namespace ContT

variable {r α β : Type u} {m : Type u → Type v}

/-- Evaluation at the trivial continuation: `lower c = c.run pure`. -/
def lower [Pure m] (c : ContT r m r) : m r := c.run pure

/-! ### Interaction with the monad operations -/

@[simp] theorem lower_pure [Pure m] (a : r) :
    lower (pure a : ContT r m r) = pure a := rfl

@[simp] theorem lower_bind [Pure m] (c : ContT r m α) (f : α → ContT r m r) :
    lower (c >>= f) = c.run λ x => lower (f x) := rfl

@[simp] theorem lower_map [Pure m] (f : α → r) (c : ContT r m α) :
    lower (f <$> c) = c.run λ x => pure (f x) := rfl

@[simp] theorem lower_seq [Pure m] (mf : ContT r m (α → r)) (mx : ContT r m α) :
    lower (mf <*> mx) = mf.run λ f => mx.run λ x => pure (f x) := rfl

/-! ### Lowering lifted computations -/

@[simp] theorem lower_monadLift [Monad m] [LawfulMonad m] (x : m r) :
    lower (monadLift x : ContT r m r) = x :=
  bind_pure x

/-- Lower, then re-lift: `reset c = monadLift (lower c)` —
[charlow-2014]'s Reset, after [danvy-filinski-1990]; [barker-2002]'s
scope-island rule is an instance. -/
def reset {r' : Type u} [Monad m] (c : ContT r m r) : ContT r' m r :=
  monadLift (lower c)

/-- `reset` is transparent to lifted effects: effects escape islands,
scope-takers do not. -/
theorem reset_monadLift {r' : Type u} [Monad m] [LawfulMonad m] (x : m r) :
    reset (monadLift x : ContT r m r) = (monadLift x : ContT r' m r) :=
  congrArg monadLift (lower_monadLift x)

/-- Lifting, combining, and lowering is just combining in `m`:
scopal combination subsumes applicative combination. -/
theorem lower_seq_monadLift [Monad m] [LawfulMonad m]
    (f : α → β → r) (x : m α) (y : m β) :
    lower (f <$> (monadLift x : ContT r m α) <*> monadLift y) =
    f <$> x <*> y := by
  simp only [lower, seq_eq_bind_map, bind_map_left, run_bind, run_map,
    run_monadLift, Function.comp_def, bind_pure_comp]

end ContT
