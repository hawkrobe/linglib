module

public import Linglib.Semantics.Causation.Graph.Defs
public import Linglib.Semantics.Causation.Valuation

/-!
# Mechanisms: structural equations

A `Mechanism G α v` is the structural equation at vertex `v` of the causal graph `G`: the value
of `v` as a function of the values of its parents, as in Pearl's structural models. Equations
are deterministic. Uncertainty is a probability on the background, not a property of the
equations (`SEM.probSufficiency`).

## Main definitions

* `Mechanism`: the structural equation at a vertex
* `Mechanism.const`: the constant equation, an exogenous default or an intervention

## References

* [pearl-2000]
-/

@[expose] public section

namespace Causation

variable {V : Type*}

/-- The structural equation at `v`: the value of `v` as a function of its parents' values. -/
abbrev Mechanism (G : CausalGraph V) (α : V → Type*) (v : V) :=
  (∀ u : G.parents v, α u.val) → α v

namespace Mechanism

variable {G : CausalGraph V} {α : V → Type*} {v : V}

/-- The constant equation, which ignores the parents: an exogenous vertex's default value, or
the equation an intervention `do(v := x)` installs. -/
def const (x : α v) : Mechanism G α v := fun _ ↦ x

@[simp] theorem const_apply (x : α v) (ρ : ∀ u : G.parents v, α u.val) :
    (const (G := G) x) ρ = x := rfl

end Mechanism

end Causation
