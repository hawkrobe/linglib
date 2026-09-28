module

public import Mathlib.Combinatorics.Digraph.Basic
public import Linglib.Core.Order.Flat
public import Linglib.Core.Order.WellFoundedFixedPoint

/-!
# Causal models

This file defines causal models in the sense of Halpern and Pearl. A causal model has a type `U`
of exogenous contexts, a value type `α v` for each endogenous variable `v`, a directed graph on
the variables (mathlib's `Digraph`), and for each variable a structural equation that gives its
value from the context and the values of its parents in the graph. An intervention holds some
variables at fixed values, and the others obey their equations (`CausalModel.step`). When the
graph is well founded, every context and every intervention determine exactly one assignment
that satisfies the equations, `CausalModel.solve`.

The solution is characterized as the unique fixed point of `step`, and it is reached by
iterating `step` from any assignment once per rank of a ranking of the graph, which is how a
finite model computes it.

## Main definitions

* `CausalModel U V α`: exogenous contexts `U`, a graph, and structural equations
* `CausalModel.IsAcyclic`: the graph is well founded
* `CausalModel.step`: one round of the equations, with the intervened variables held fixed
* `CausalModel.solve`: the solution under an intervention in a context

## Main results

* `CausalModel.isFixedPt_solve`, `CausalModel.eq_solve_of_isFixedPt`: the solution is the unique
  fixed point of `step`
* `CausalModel.solve_eq_iterate`, `CausalModel.solve_eq_iterate_card`: iterating `step` past a
  ranking of the graph reaches it

## Implementation notes

An equation reads the whole assignment, and `dependsOn_eqn` says that it only reads the parents
(mathlib's `DependsOn`), so equations are written without the parents' subtype. The graph is data,
the edges a paper draws, and bounds what an equation may read rather than recording what it does
read. An intervention is a partial assignment `∀ v, Flat (α v)`, the variables it settles being the
intervened ones. The solution is `WellFounded.fixedPoint` of `step`, whose construction fills the
coordinates an equation ignores arbitrarily, hence `[∀ v, Nonempty (α v)]`.

## References

* [halpern-pearl-2005]
* [pearl-2000]
-/

@[expose] public section

/-- A causal model is a directed graph on the variables `V` with a structural equation at each
variable. The equation gives the variable's value in `α v` from an exogenous context in `U` and
the values of the variable's parents, the sources of its incoming edges. -/
structure CausalModel (U V : Type*) (α : V → Type*) where
  /-- The causal graph, with an edge from `w` to `v` when `v`'s equation may read `w`. -/
  graph : Digraph V
  /-- The structural equation of each variable, read in a context. -/
  eqn : ∀ v, U → (∀ w, α w) → α v
  /-- Each equation reads only the variable's parents. -/
  dependsOn_eqn : ∀ v u, DependsOn (eqn v u) {w | graph.Adj w v}

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α)

/-- A model is acyclic, or recursive, when its graph is well founded. -/
abbrev IsAcyclic : Prop := WellFounded M.graph.Adj

/-- A model is acyclic when every edge climbs in depth. -/
theorem IsAcyclic.of_depth (depth : V → ℕ) (h : ∀ {w v}, M.graph.Adj w v → depth w < depth v) :
    M.IsAcyclic :=
  RelHomClass.wellFounded (⟨depth, h⟩ : M.graph.Adj →r (· < ·)) wellFounded_lt

/-- `M.step I u x` applies the equations once in the context `u`. A variable the intervention
`I` settles takes its intervened value, and any other variable takes the value its equation
gives to `x`. -/
def step (I : ∀ v, Flat (α v)) (u : U) (x : ∀ v, α v) : ∀ v, α v :=
  fun v ↦ (I v).unbotD (M.eqn v u x)

variable {M}

theorem step_apply (I : ∀ v, Flat (α v)) (u : U) (x : ∀ v, α v) (v : V) :
    M.step I u x v = (I v).unbotD (M.eqn v u x) := rfl

/-- Each round computes a variable from its parents. -/
theorem dependsOn_step (I : ∀ v, Flat (α v)) (u : U) (v : V) :
    DependsOn (M.step I u · v) {w | M.graph.Adj w v} :=
  fun _ _ h ↦ congrArg (Flat.unbotD · (I v)) (M.dependsOn_eqn v u h)

/-- After `k` rounds of the equations, a variable of rank below `k` no longer depends on the
assignment the rounds started from. -/
theorem iterate_step_apply_eq (r : M.graph.Adj →r ((· < ·) : ℕ → ℕ → Prop))
    (I : ∀ v, Flat (α v)) (u : U) {k : ℕ} {v : V} (hv : r v < k) (x y : ∀ v, α v) :
    (M.step I u)^[k] x v = (M.step I u)^[k] y v :=
  WellFounded.iterate_apply_eq_of_dependsOn (dependsOn_step I u) r hv x y

section Solve

variable (M) [∀ v, Nonempty (α v)] [hM : M.IsAcyclic]

/-- The solution of the model under the intervention `I` in the context `u`, the unique fixed
point of `step`. -/
noncomputable def solve (I : ∀ v, Flat (α v)) (u : U) : ∀ v, α v :=
  hM.fixedPoint (M.step I u)

/-- The solution satisfies the equations. -/
theorem isFixedPt_solve (I : ∀ v, Flat (α v)) (u : U) :
    Function.IsFixedPt (M.step I u) (M.solve I u) :=
  hM.isFixedPt_fixedPoint (dependsOn_step I u)

variable {M}

/-- An assignment satisfying the equations is the solution. -/
theorem eq_solve_of_isFixedPt {I : ∀ v, Flat (α v)} {u : U} {x : ∀ v, α v}
    (hx : Function.IsFixedPt (M.step I u) x) : x = M.solve I u :=
  WellFounded.eq_fixedPoint_of_isFixedPt (dependsOn_step I u) hx

theorem isFixedPt_iff_eq_solve {I : ∀ v, Flat (α v)} {u : U} {x : ∀ v, α v} :
    Function.IsFixedPt (M.step I u) x ↔ x = M.solve I u :=
  WellFounded.isFixedPt_iff_eq_fixedPoint (dependsOn_step I u)

theorem solve_apply (I : ∀ v, Flat (α v)) (u : U) (v : V) :
    M.solve I u v = (I v).unbotD (M.eqn v u (M.solve I u)) :=
  WellFounded.fixedPoint_apply (dependsOn_step I u) v

/-- An intervened variable takes its intervened value. -/
theorem solve_of_eq_coe {I : ∀ v, Flat (α v)} {v : V} {x : α v} (h : I v = ↑x) (u : U) :
    M.solve I u v = x := by
  rw [solve_apply, h, Flat.unbotD_coe]

/-- A variable the intervention leaves alone obeys its equation. -/
theorem solve_of_eq_bot {I : ∀ v, Flat (α v)} {v : V} (h : I v = ⊥) (u : U) :
    M.solve I u v = M.eqn v u (M.solve I u) := by
  rw [solve_apply, h, Flat.unbotD_bot]

/-- Iterating the equations from any assignment past a ranking of the graph reaches the
solution. -/
theorem solve_eq_iterate (r : M.graph.Adj →r ((· < ·) : ℕ → ℕ → Prop)) {n : ℕ}
    (hn : ∀ v, r v < n) (I : ∀ v, Flat (α v)) (u : U) (x : ∀ v, α v) :
    M.solve I u = (M.step I u)^[n] x :=
  WellFounded.fixedPoint_eq_iterate (dependsOn_step I u) r hn x

/-- In a finite model, iterating the equations once per variable reaches the solution. -/
theorem solve_eq_iterate_card [Fintype V] (I : ∀ v, Flat (α v)) (u : U) (x : ∀ v, α v) :
    M.solve I u = (M.step I u)^[Fintype.card V] x :=
  WellFounded.fixedPoint_eq_iterate_card (dependsOn_step I u) x

end Solve

end CausalModel
