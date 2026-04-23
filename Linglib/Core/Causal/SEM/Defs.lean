import Linglib.Core.Causal.Graph.Basic
import Linglib.Core.Causal.Mechanism.Defs
import Linglib.Core.Causal.Valuation

/-!
# SEM: Bundled Structural Equation Model (V2)

A `SEM V α` is a `CausalGraph V` together with a `Mechanism` for every
vertex. Replaces the old `CausalDynamics` (which conflated the implicit
graph topology with the precondition-list mechanism content into a
single `List CausalLaw`).

`IsDeterministic` and `IsBool` are `Prop` mixin classes that consumers
can require — mirroring the mathlib pattern where typeclass mixins
mark properties of a structure value (`IsMarkovKernel` etc.).

Phase A scope: structure + mixins only. Forward propagation, intervention,
and counterfactual queries live in `SEM/Basic.lean`.
-/

namespace Core.Causal

/-- A **structural equation model**: a causal graph with a mechanism at
    every vertex over a per-vertex value type `α`.

    Replaces the old `CausalDynamics`. The graph topology is now
    explicit (`graph.parents v`) and separate from mechanism content
    (`mech v`); the value type is parameterized (`α : V → Type*`)
    instead of hardcoded `Bool`. -/
structure SEM (V : Type*) (α : V → Type*) where
  /-- The underlying causal graph (parent finsets per vertex). -/
  graph : CausalGraph V
  /-- The mechanism at each vertex: parent values ↦ distribution over `α v`. -/
  mech  : ∀ v, Mechanism graph α v

namespace SEM

variable {V : Type*} {α : V → Type*}

/-- The SEM is fully **deterministic**: every vertex's mechanism is Dirac. -/
class IsDeterministic (M : SEM V α) where
  mech_det : ∀ v, Mechanism.IsDeterministic (M.mech v)

/-- Project per-vertex `Mechanism.IsDeterministic` from `SEM.IsDeterministic`. -/
instance (M : SEM V α) [h : IsDeterministic M] (v : V) :
    Mechanism.IsDeterministic (M.mech v) := h.mech_det v

end SEM


end Core.Causal
