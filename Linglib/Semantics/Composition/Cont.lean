import Mathlib.Control.Monad.Cont

/-!
# Evaluating continuation computations

`ContT.eval` finishes a continuation computation by handing it the
trivial continuation `pure` — [charlow-2014]'s Lowering, Haskell's
`evalCont`, the LOWER of [barker-shan-2014]. The `eval_*` simp lemmas
mirror `ContT`'s `run_*` set: a chain of binds evaluates in bind order
and the applicative combination left-to-right, which is what lets bind
order model quantifier scope. `ContT.reset` evaluates and re-lifts,
delimiting scope the way scope islands do. For the linguistic
applications see `Studies/BumfordCharlow2024.lean` and
`Studies/Charlow2020.lean`.

## References

- <https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html#v:evalCont>
-/

universe u v

namespace ContT

variable {r α β : Type u} {m : Type u → Type v}

/-- Evaluation at the trivial continuation: `eval c = c.run pure`. -/
def eval [Pure m] (c : ContT r m r) : m r := c.run pure

/-! ### Interaction with the monad operations -/

@[simp] theorem eval_pure [Pure m] (a : r) :
    eval (pure a : ContT r m r) = pure a := rfl

@[simp] theorem eval_bind [Pure m] (c : ContT r m α) (f : α → ContT r m r) :
    eval (c >>= f) = c.run λ x => eval (f x) := rfl

@[simp] theorem eval_map [Pure m] (f : α → r) (c : ContT r m α) :
    eval (f <$> c) = c.run λ x => pure (f x) := rfl

@[simp] theorem eval_seq [Pure m] (mf : ContT r m (α → r)) (mx : ContT r m α) :
    eval (mf <*> mx) = mf.run λ f => mx.run λ x => pure (f x) := rfl

/-! ### Evaluating lifted computations -/

@[simp] theorem eval_monadLift [Monad m] [LawfulMonad m] (x : m r) :
    eval (monadLift x : ContT r m r) = x :=
  bind_pure x

/-- Evaluate, then re-lift: `reset c = monadLift (eval c)` —
[charlow-2014]'s Reset, after [danvy-filinski-1990]; [barker-2002]'s
scope-island rule is an instance. -/
def reset {r' : Type u} [Monad m] (c : ContT r m r) : ContT r' m r :=
  monadLift (eval c)

/-- `reset` is transparent to lifted effects: effects escape islands,
scope-takers do not. -/
theorem reset_monadLift {r' : Type u} [Monad m] [LawfulMonad m] (x : m r) :
    reset (monadLift x : ContT r m r) = (monadLift x : ContT r' m r) :=
  congrArg monadLift (eval_monadLift x)

/-- Lifting, combining, and evaluating is just combining in `m`:
scopal combination subsumes applicative combination. -/
theorem eval_seq_monadLift [Monad m] [LawfulMonad m]
    (f : α → β → r) (x : m α) (y : m β) :
    eval (f <$> (monadLift x : ContT r m α) <*> monadLift y) =
    f <$> x <*> y := by
  simp only [eval, seq_eq_bind_map, bind_map_left, run_bind, run_map,
    run_monadLift, Function.comp_def, bind_pure_comp]

/-- Evaluating a lifted computation under a value-level map is mapping in `m`. -/
theorem eval_map_monadLift [Monad m] [LawfulMonad m] (f : α → r) (x : m α) :
    eval (f <$> (monadLift x : ContT r m α)) = f <$> x := by
  simp only [eval_map, run_monadLift, bind_pure_comp]

/-- Resetting a lifted computation changes nothing, whatever sits on the bottom level
([charlow-2014]'s Fact 4.1): evaluation leaves the side effects of the underlying monad
intact. -/
theorem reset_map_monadLift {r' : Type u} [Monad m] [LawfulMonad m] (f : α → r) (x : m α) :
    reset (f <$> (monadLift x : ContT r m α)) = (monadLift (f <$> x) : ContT r' m r) :=
  congrArg monadLift (eval_map_monadLift f x)

/-- Resetting a combination of lifted computations is lifting their combination in `m`. -/
theorem reset_seq_monadLift {r' : Type u} [Monad m] [LawfulMonad m]
    (f : α → β → r) (x : m α) (y : m β) :
    reset (f <$> (monadLift x : ContT r m α) <*> monadLift y) =
      (monadLift (f <$> x <*> y) : ContT r' m r) :=
  congrArg monadLift (eval_seq_monadLift f x y)

end ContT
