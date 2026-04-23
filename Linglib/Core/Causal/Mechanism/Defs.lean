import Linglib.Core.Causal.Graph.Defs
import Linglib.Core.Causal.Valuation
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Mechanism: PMF-Valued Structural Equation per Vertex (V2)

A `Mechanism G α v` is the structural equation at vertex `v`: it takes
a value assignment to `v`'s parents and returns a `PMF (α v)` — a
probability distribution over possible values of `v`.

This single type unifies deterministic and stochastic mechanisms via the
mathlib `Kernel.deterministic := dirac ∘ f` pattern (see
`Mathlib/Probability/Kernel/Basic.lean`):
- Deterministic mechanism = PMF.pure-valued (Dirac delta) — see
  `Mechanism/Deterministic.lean`
- Stochastic mechanism = arbitrary PMF — see `Mechanism/PMF.lean`

`IsDeterministic` is a `Prop` mixin class that consumers can require
when they need to extract the deterministic function (mirroring
`IsMarkovKernel` in `Mathlib/Probability/Kernel/Defs.lean`).
-/

namespace Core.Causal

variable {V : Type*}

/-- A causal mechanism for vertex `v` in graph `G`: takes a value
    assignment to `v`'s parents and returns a distribution over `α v`.
    PMF-valued so deterministic and stochastic mechanisms share one type
    (deterministic = Dirac PMF). -/
structure Mechanism (G : CausalGraph V) (α : V → Type*) (v : V) where
  /-- The structural function: parent assignment ↦ distribution over v's value. -/
  run : (∀ u : G.parents v, α u.val) → PMF (α v)

namespace Mechanism

variable {α : V → Type*} {G : CausalGraph V} {v : V}

/-- A mechanism is **deterministic** when it carries an explicit total
    function over parents whose lifting via `PMF.pure` agrees with `run`.

    Data-carrying class (not `Prop`) so consumers can extract `toFun`
    computably. Compare mathlib `Module R M` (data-carrying) vs
    `IsMarkovKernel` (`Prop`); we choose data-carrying because the
    underlying function is uniquely determined and useful in proofs. -/
class IsDeterministic (m : Mechanism G α v) where
  /-- The deterministic function over parent assignments. -/
  toFun : (∀ u : G.parents v, α u.val) → α v
  /-- The mechanism's `run` is the Dirac of `toFun`. -/
  run_eq : ∀ ρ, m.run ρ = PMF.pure (toFun ρ)

end Mechanism

end Core.Causal
