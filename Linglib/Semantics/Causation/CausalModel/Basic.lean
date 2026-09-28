module

public import Linglib.Semantics.Causation.CausalModel.Defs

/-!
# Observation and intervention in causal models

A partial assignment `s : ∀ v, Flat (α v)` can be read two ways in a causal model. As an
intervention it holds the variables it settles at their values (`CausalModel.solve`). As an
observation it picks out the contexts whose actual world agrees with it, `CausalModel.contexts`.
This file relates the two readings.

The solution at a variable depends only on the intervention at that variable and its ancestors
(`CausalModel.solve_congr`), so an intervention leaves every variable it cannot reach as it was
(`CausalModel.solve_update_of_not_reflTransGen`). A counterfactual is then evaluated in the
three steps of Pearl: condition on the contexts where the observation holds, intervene, and
solve. Lassiter's rewind–revise–regenerate procedure keeps the observed value of every variable
causally independent of the antecedent and regenerates the rest; with exogenous contexts that
is a theorem rather than a construction (`CausalModel.solve_update_eq_of_mem_contexts`).

## Main definitions

* `CausalModel.world`: the actual world of a context, as a total partial assignment
* `CausalModel.contexts`: the contexts in which an observation holds

## Main results

* `CausalModel.solve_congr`: interventions agreeing on a variable's ancestors agree there
* `CausalModel.solve_update_of_not_reflTransGen`: intervening on `c` leaves what `c` does not
  reach unchanged
* `CausalModel.solve_update_eq_of_mem_contexts`: a counterfactual keeps every observed value
  the antecedent does not reach

## References

* [pearl-2000]
* [lassiter-2017-probabilistic-language]
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

theorem mem_contexts {s : ∀ v, Flat (α v)} {u : U} :
    u ∈ M.contexts s ↔ ∀ v (x : α v), s v = ↑x → M.solve ⊥ u v = x := by
  refine forall_congr' fun v ↦ ?_
  cases s v with
  | bot => simp
  | coe x => simp [world, Flat.coe_le_coe, eq_comm]

@[simp] theorem contexts_bot : M.contexts ⊥ = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ bot_le

/-- Observing more leaves fewer contexts. -/
theorem contexts_anti : Antitone M.contexts :=
  fun _ _ hst _ hu ↦ hst.trans hu

/-- In a context where `s` is observed, setting `c := x` leaves every observed variable that `c`
does not reach at its observed value, the step of rewind–revise–regenerate that keeps what is
causally independent of the antecedent. -/
theorem solve_update_eq_of_mem_contexts [DecidableEq V] {s : ∀ v, Flat (α v)} {u : U}
    (hu : u ∈ M.contexts s) {c w : V} (hcw : ¬ ReflTransGen M.graph.Adj c w) {y : α w}
    (hs : s w = ↑y) (x : α c) : M.solve (Function.update ⊥ c ↑x) u w = y := by
  rw [solve_update_of_not_reflTransGen hcw]
  exact mem_contexts.1 hu w y hs

end Observation

end CausalModel
