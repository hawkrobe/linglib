module

public import Linglib.Core.Relation.FactorsThroughOn
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Restrict
public import Mathlib.Order.UpperLower.Basic

/-!
# Dependence and variation atoms

This file defines the two atoms of first-order team semantics over a team of assignments: the
dependence atom of [vaananen-2007], that assignments agreeing on the parameters agree on the
dependent variable, and its failure, the variation atom, that two assignments agreeing on the
parameters differ on it. Dependence is functional dependence: on the team, evaluation at the
dependent variable factors through restriction to the parameters, so the value of the variable
is a function of the values of the parameters.

Widening the parameters weakens dependence and strengthens variation, which is how the atoms
compose into the constancy and variation conditions of [degano-aloni-2025]. Dependence is
inherited by subteams and variation by superteams, so both atoms define convex team properties.
Teams are finite so that the atoms are decidable over a finite domain.

## Main definitions

* `Team.Dep`: the dependence atom.
* `Team.Var`: the variation atom.

## Main results

* `Team.dep_iff_exists`: the dependent variable is a function of the parameters on the team.
* `Team.not_dep`: variation is the failure of dependence.
* `Team.Dep.trans`: dependence composes.
* `Team.isLowerSet_dep`, `Team.isUpperSet_var`: closure under subteams and superteams.

## References

* [hodges-1997]
* [vaananen-2007]
* [degano-aloni-2025]
-/

@[expose] public section

namespace Team

variable {V E : Type*} {T T' : Finset (V → E)} {Z Z' : Finset V} {u : V}

/-- The dependence atom `dep(Z, u)`: on the team, the value of `u` factors through the values of
the variables of `Z`; with `Z` empty, `u` is constant across the team. -/
def Dep (T : Finset (V → E)) (Z : Finset V) (u : V) : Prop :=
  Function.FactorsThroughOn (· u) (Z : Set V).domRestrict (T : Set (V → E))

/-- The variation atom `var(Z, u)`: two assignments of the team agree on `Z` and differ on
`u`. -/
def Var (T : Finset (V → E)) (Z : Finset V) (u : V) : Prop :=
  ∃ i ∈ T, ∃ j ∈ T, (∀ z ∈ Z, i z = j z) ∧ i u ≠ j u

/-- Assignments of the team agreeing on every variable of `Z` agree on `u`. -/
theorem dep_iff : Dep T Z u ↔ ∀ i ∈ T, ∀ j ∈ T, (∀ z ∈ Z, i z = j z) → i u = j u := by
  simp only [Dep, Function.FactorsThroughOn, Set.domRestrict_eq_domRestrict_iff, Set.EqOn,
    Finset.mem_coe]
  exact ⟨fun h i hi j hj hZ ↦ h hi hj hZ, fun h i j hi hj hZ ↦ h i hi j hj hZ⟩

instance [DecidableEq E] (T : Finset (V → E)) (Z : Finset V) (u : V) : Decidable (Dep T Z u) :=
  decidable_of_iff _ dep_iff.symm

instance [DecidableEq E] (T : Finset (V → E)) (Z : Finset V) (u : V) : Decidable (Var T Z u) :=
  inferInstanceAs (Decidable (∃ i ∈ T, ∃ j ∈ T, (∀ z ∈ Z, i z = j z) ∧ i u ≠ j u))

/-- Functional dependence, existentially: on the team, the value of `u` is a function of the
values of the variables of `Z`. -/
theorem dep_iff_exists [Nonempty E] :
    Dep T Z u ↔ ∃ h : (Z → E) → E, ∀ i ∈ T, i u = h ((Z : Set V).domRestrict i) :=
  Function.factorsThroughOn_iff_exists_eqOn

/-- Variation is the failure of dependence. -/
@[simp]
theorem not_dep : ¬ Dep T Z u ↔ Var T Z u := by
  simp only [dep_iff, Var, not_forall, exists_prop]

@[simp]
theorem not_var : ¬ Var T Z u ↔ Dep T Z u := by rw [← not_dep, not_not]

/-- Dependence excludes variation on the same parameters. -/
theorem Dep.not_var (h : Dep T Z u) : ¬ Var T Z u := Team.not_var.2 h

/-- A parameter depends on the parameters. -/
theorem dep_of_mem (h : u ∈ Z) : Dep T Z u := dep_iff.2 fun _ _ _ _ hZ ↦ hZ u h

/-- Every dependence holds on a team of one assignment. -/
theorem dep_singleton (i : V → E) : Dep {i} Z u :=
  dep_iff.2 fun _ hi _ hj _ ↦ by rw [Finset.mem_singleton.1 hi, Finset.mem_singleton.1 hj]

/-- Dependence on fewer parameters is dependence on more. -/
theorem Dep.mono (hZ : Z ⊆ Z') (h : Dep T Z u) : Dep T Z' u :=
  dep_iff.2 fun i hi j hj hagree ↦ dep_iff.1 h i hi j hj fun z hz ↦ hagree z (hZ hz)

/-- Variation on more parameters is variation on fewer. -/
theorem Var.anti (hZ : Z ⊆ Z') (h : Var T Z' u) : Var T Z u :=
  let ⟨i, hi, j, hj, hagree, hne⟩ := h
  ⟨i, hi, j, hj, fun z hz ↦ hagree z (hZ hz), hne⟩

/-- Dependence composes: a variable depending on variables that all depend on `Z` depends on
`Z`. -/
theorem Dep.trans (hZ : ∀ z ∈ Z', Dep T Z z) (h : Dep T Z' u) : Dep T Z u :=
  dep_iff.2 fun i hi j hj hagree ↦
    dep_iff.1 h i hi j hj fun z hz ↦ dep_iff.1 (hZ z hz) i hi j hj hagree

/-- Dependence is inherited by subteams. -/
theorem Dep.subset (hT : T' ⊆ T) (h : Dep T Z u) : Dep T' Z u :=
  Function.FactorsThroughOn.mono h (Finset.coe_subset.2 hT)

/-- Variation is inherited by superteams. -/
theorem Var.superset (hT : T ⊆ T') (h : Var T Z u) : Var T' Z u :=
  let ⟨i, hi, j, hj, hagree, hne⟩ := h
  ⟨i, hT hi, j, hT hj, hagree, hne⟩

theorem isLowerSet_dep (Z : Finset V) (u : V) : IsLowerSet {T : Finset (V → E) | Dep T Z u} :=
  fun _ _ hT h ↦ h.subset hT

theorem isUpperSet_var (Z : Finset V) (u : V) : IsUpperSet {T : Finset (V → E) | Var T Z u} :=
  fun _ _ hT h ↦ h.superset hT

end Team
