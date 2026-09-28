module

public import Linglib.Semantics.Causation.CausalModel.Defs
public import Linglib.Semantics.Causation.SEM.Deterministic

/-!
# Structural equation models as causal models

This file shows that a structural equation model (`SEM`) is a causal model with a single
exogenous context, and that its eager development `SEM.developDet` is the solution of that causal
model, with the developed valuation as the intervention. The development's lemmas therefore
follow from the fixed-point characterization of `CausalModel.solve`.

## Main definitions

* `SEM.toCausalModel`: the causal model of a structural equation model, over `Unit`

## Main results

* `SEM.developDetVtx_eq_solve`: eager development is the solution of that causal model

## References

* [pearl-2000]
-/

@[expose] public section

namespace Causation.SEM

variable {V : Type*} {α : V → Type*}

/-- A structural equation model is a causal model with a single exogenous context. -/
def toCausalModel (M : SEM V α) : CausalModel Unit V α where
  graph := ⟨fun w v ↦ w ∈ M.graph.parents v⟩
  eqn v _ x := M.mech v fun w ↦ x w
  dependsOn_eqn v _ _ _ h := congrArg (M.mech v) (funext fun w ↦ h w w.2)

variable (M : SEM V α)

@[simp] theorem toCausalModel_adj {w v : V} :
    M.toCausalModel.graph.Adj w v ↔ w ∈ M.graph.parents v := Iff.rfl

instance [h : M.graph.IsDAG] : M.toCausalModel.IsAcyclic :=
  Subrelation.wf (fun h ↦ .single h) h

variable [M.graph.IsDAG] [∀ v, Nonempty (α v)]

/-- Eager development is the solution of the causal model, the valuation being the
intervention. -/
theorem developDetVtx_eq_solve (s : Valuation α) :
    developDetVtx M s = M.toCausalModel.solve s () := by
  refine CausalModel.eq_solve_of_isFixedPt (funext fun v ↦ ?_)
  rw [CausalModel.step_apply, developDetVtx_unfold, Valuation.get]
  cases s v <;> rfl

end Causation.SEM
