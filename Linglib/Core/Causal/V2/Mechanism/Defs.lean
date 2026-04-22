import Linglib.Core.Causal.V2.Graph.Defs
import Linglib.Core.Causal.V2.Valuation
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

namespace Core.Causal.V2

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

/-- A mechanism is **deterministic** iff every parent assignment yields
    a Dirac PMF (singleton support).

    Mathlib analogue: `IsMarkovKernel` from `Mathlib/Probability/Kernel/Defs.lean`
    — a `Prop` class on a value of the structure, marking a property
    that operations may require. -/
class IsDeterministic (m : Mechanism G α v) : Prop where
  /-- Every input has a unique output value (Dirac support). -/
  pure_run : ∀ ρ : ∀ u : G.parents v, α u.val,
    ∃ x : α v, m.run ρ = PMF.pure x

end Mechanism

end Core.Causal.V2
