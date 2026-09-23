module

public import Linglib.Semantics.Causation.Graph.Basic
public import Linglib.Semantics.Causation.Mechanism.Defs
public import Linglib.Semantics.Causation.Valuation

/-!
# Structural equation models

A `SEM V α` is a `CausalGraph V` together with a structural equation (`Mechanism`) at every
vertex, the value types varying with the vertex. Development, intervention and counterfactuals
live in `SEM/Basic.lean`, `SEM/Deterministic.lean` and `SEM/Counterfactual.lean`.

## References

* [pearl-2000]
-/

@[expose] public section

namespace Causation

/-- A **structural equation model**: a causal graph with a structural equation at every vertex,
over a per-vertex value type `α`. -/
structure SEM (V : Type*) (α : V → Type*) where
  /-- The underlying causal graph (parent finsets per vertex). -/
  graph : CausalGraph V
  /-- The structural equation at each vertex: parent values ↦ value. -/
  mech  : ∀ v, Mechanism graph α v

end Causation
