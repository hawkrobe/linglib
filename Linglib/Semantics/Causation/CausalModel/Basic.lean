module

public import Linglib.Semantics.Causation.CausalModel.Defs

/-!
# Observation and intervention in causal models

A partial assignment `s : ∀ v, Flat (α v)` can be read two ways in a causal model. As an
intervention it holds the variables it settles at their values (`CausalModel.solve`). As an
observation it picks out the contexts whose actual world agrees with it,
`CausalModel.contexts`, the conditioning step of Pearl's evaluation of a counterfactual.

The solution at a variable depends only on the intervention at that variable and its ancestors
(`CausalModel.solve_congr`), so an intervention leaves every variable it cannot reach as it was
(`CausalModel.solve_update_of_not_reflTransGen`).

## Main definitions

* `CausalModel.world`: the actual world of a context, as a total partial assignment
* `CausalModel.contexts`: the contexts in which an observation holds

## Main results

* `CausalModel.solve_congr`: interventions agreeing on a variable's ancestors agree there
* `CausalModel.solve_update_of_not_reflTransGen`: intervening on `c` leaves what `c` does not
  reach unchanged

## References

* [pearl-2000]
-/

@[expose] public section

namespace CausalModel

open Relation

variable {U V : Type*} {α : V → Type*} {M : CausalModel U V α} [∀ v, Nonempty (α v)]
  [hM : M.IsAcyclic]

section Locality

/-- Interventions that agree on a variable and all its ancestors give it the same value. -/
theorem solve_congr {I J : ∀ v, Flat (α v)} {v : V}
    (h : ∀ w, ReflTransGen M.graph.Adj w v → I w = J w) (u : U) :
    M.solve I u v = M.solve J u v := by
  induction v using hM.induction with
  | _ v ih =>
    rw [solve_apply, solve_apply, h v .refl]
    congr 1
    exact M.dependsOn_eqn v u fun w (hw : M.graph.Adj w v) ↦
      ih w hw fun w' hw' ↦ h w' (hw'.tail hw)

variable [DecidableEq V]

@[simp] theorem solve_update_self (I : ∀ v, Flat (α v)) (c : V) (x : α c) (u : U) :
    M.solve (Function.update I c ↑x) u c = x :=
  solve_of_eq_coe (Function.update_self ..) u

/-- Intervening on `c` leaves every variable that `c` is not an ancestor of unchanged. -/
theorem solve_update_of_not_reflTransGen {c v : V} (h : ¬ ReflTransGen M.graph.Adj c v)
    (I : ∀ v, Flat (α v)) (x : Flat (α c)) (u : U) :
    M.solve (Function.update I c x) u v = M.solve I u v :=
  solve_congr (fun w hw ↦ Function.update_of_ne (fun hwc : w = c ↦ h (hwc ▸ hw)) x I) u

end Locality

section Observation

variable (M)

/-- `M.world u` is the actual world of the context `u`, the solution under no intervention with
every variable settled. -/
noncomputable def world (u : U) : ∀ v, Flat (α v) := fun v ↦ ↑(M.solve ⊥ u v)

/-- `M.contexts s` is the set of contexts in which the observation `s` holds, those whose actual
world settles every variable `s` settles, at the same value. -/
def contexts (s : ∀ v, Flat (α v)) : Set U := {u | s ≤ M.world u}

variable {M}

@[simp] theorem contexts_bot : M.contexts ⊥ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ bot_le

end Observation

end CausalModel
