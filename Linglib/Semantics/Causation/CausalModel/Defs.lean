module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Logic.Function.Iterate
public import Linglib.Semantics.Causation.Graph.Basic
public import Linglib.Semantics.Causation.Valuation

/-!
# Causal models

This file defines causal models in the sense of Halpern and Pearl. A causal model has a type `U`
of exogenous contexts, a value type `α v` for each endogenous variable `v`, and a structural
equation for each variable that gives its value from the context and the values of its parents
in a causal graph. An intervention holds some variables at fixed values, and the others obey
their equations (`CausalModel.step`). When the graph is acyclic, every context and every
intervention determine exactly one assignment that satisfies the equations, `CausalModel.solve`.

The solution is characterized as the unique fixed point of `step`, and it is reached by
iterating `step` from any assignment once per rank of a ranking of the graph, which is how a
finite model computes it.

## Main definitions

* `CausalModel U V α`: exogenous contexts `U` and structural equations over a causal graph
* `CausalModel.step`: one round of the equations, with the intervened variables held fixed
* `CausalModel.solve`: the solution under an intervention in a context

## Main results

* `CausalModel.isFixedPt_solve`, `CausalModel.eq_solve_of_isFixedPt`: the solution is the unique
  fixed point of `step`
* `CausalModel.solve_eq_iterate`: iterating `step` past a ranking of the graph reaches it

## Implementation notes

An equation reads the whole assignment, and `dependsOn_eqn` says that it only reads the parents
(mathlib's `DependsOn`), so equations are written without the parents' subtype. An intervention
is a `Valuation`, the variables it settles being the intervened ones. Building the
solution by well-founded recursion feeds each equation the recursive values at the parents and an
arbitrary value elsewhere, hence `[∀ v, Nonempty (α v)]`.

## References

* [halpern-pearl-2005]
* [pearl-2000]
-/

@[expose] public section

open Causation

/-- A causal model puts a structural equation on each variable of a causal graph on `V`. The
equation gives the variable's value in `α v` from an exogenous context in `U` and the values of
the variable's parents. -/
structure CausalModel (U V : Type*) (α : V → Type*) where
  /-- The causal graph. -/
  graph : CausalGraph V
  /-- The structural equation of each variable, read in a context. -/
  eqn : ∀ v, U → (∀ w, α w) → α v
  /-- Each equation reads only the variable's parents. -/
  dependsOn_eqn : ∀ v u, DependsOn (eqn v u) (graph.parents v)

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α)

/-- `M.step I u x` applies the equations once in the context `u`. A variable the intervention
`I` settles takes its intervened value, and any other variable takes the value its equation
gives to `x`. -/
def step (I : Valuation α) (u : U) (x : ∀ v, α v) : ∀ v, α v :=
  fun v ↦ (I.get v).getD (M.eqn v u x)

variable {M}

theorem step_apply (I : Valuation α) (u : U) (x : ∀ v, α v) (v : V) :
    M.step I u x v = (I.get v).getD (M.eqn v u x) := rfl

/-- After `k` rounds of the equations, a variable of rank below `k` no longer depends on the
assignment the rounds started from. -/
theorem iterate_step_apply_eq (r : M.graph.Ranking) (I : Valuation α) (u : U) {k : ℕ} {v : V}
    (hv : r v < k) (x y : ∀ v, α v) : (M.step I u)^[k] x v = (M.step I u)^[k] y v := by
  induction k generalizing v with
  | zero => omega
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', step_apply, step_apply]
    congr 1
    exact M.dependsOn_eqn v u fun w hw ↦ ih (by have := r.map_rel (Finset.mem_coe.1 hw); omega)

section Solve

variable (M) [∀ v, Nonempty (α v)] [hG : M.graph.IsDAG]

open Classical in
/-- The solution of the model under the intervention `I` in the context `u`, by well-founded
recursion on the graph. -/
noncomputable def solve (I : Valuation α) (u : U) : ∀ v, α v :=
  hG.fix fun v rec ↦ (I.get v).getD <| M.eqn v u fun w ↦
    if h : w ∈ M.graph.parents v then rec w (.single h) else Classical.arbitrary _

/-- The solution satisfies the equations. -/
theorem isFixedPt_solve (I : Valuation α) (u : U) :
    Function.IsFixedPt (M.step I u) (M.solve I u) := by
  funext v
  conv_rhs => rw [solve, WellFounded.fix_eq]
  rw [step_apply]
  congr 1
  exact M.dependsOn_eqn v u fun w hw ↦ by simp only [Finset.mem_coe.1 hw, ↓reduceDIte]; rfl

variable {M}

/-- An assignment satisfying the equations is the solution. -/
theorem eq_solve_of_isFixedPt {I : Valuation α} {u : U} {x : ∀ v, α v}
    (hx : Function.IsFixedPt (M.step I u) x) : x = M.solve I u := by
  funext v
  induction v using hG.induction with
  | _ v ih =>
    rw [← congrFun hx v, ← congrFun (M.isFixedPt_solve I u) v, step_apply, step_apply]
    congr 1
    exact M.dependsOn_eqn v u fun w hw ↦ ih w (.single (Finset.mem_coe.1 hw))

theorem isFixedPt_iff_eq_solve {I : Valuation α} {u : U} {x : ∀ v, α v} :
    Function.IsFixedPt (M.step I u) x ↔ x = M.solve I u :=
  ⟨eq_solve_of_isFixedPt, fun h ↦ h ▸ M.isFixedPt_solve I u⟩

theorem solve_apply (I : Valuation α) (u : U) (v : V) :
    M.solve I u v = (I.get v).getD (M.eqn v u (M.solve I u)) :=
  (congrFun (M.isFixedPt_solve I u) v).symm

/-- An intervened variable takes its intervened value. -/
theorem solve_of_get_eq_some {I : Valuation α} {v : V} {x : α v} (h : I.get v = some x)
    (u : U) : M.solve I u v = x := by
  rw [solve_apply, h, Option.getD_some]

/-- A variable the intervention leaves alone obeys its equation. -/
theorem solve_of_get_eq_none {I : Valuation α} {v : V} (h : I.get v = none) (u : U) :
    M.solve I u v = M.eqn v u (M.solve I u) := by
  rw [solve_apply, h, Option.getD_none]

/-- Iterating the equations from any assignment past a ranking of the graph reaches the
solution. -/
theorem solve_eq_iterate (r : M.graph.Ranking) {n : ℕ} (hn : ∀ v, r v < n) (I : Valuation α)
    (u : U) (x : ∀ v, α v) : M.solve I u = (M.step I u)^[n] x := by
  funext v
  rw [← (M.isFixedPt_solve I u).iterate n]
  exact iterate_step_apply_eq r I u (hn v) _ _

/-- In a finite model, iterating the equations once per variable reaches the solution. -/
theorem solve_eq_iterate_card [Fintype V] [DecidableEq V] (I : Valuation α) (u : U)
    (x : ∀ v, α v) : M.solve I u = (M.step I u)^[Fintype.card V] x :=
  solve_eq_iterate M.graph.ancestorRanking (M.graph.ancestorRanking_lt_card) I u x

end Solve

end CausalModel
