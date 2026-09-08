import Mathlib.Data.Finset.Basic

/-!
# Dependence and variation atoms

This file defines the two atoms of first-order team semantics over a team of assignments: the
dependence atom of [vaananen-2007], that assignments agreeing on the parameters agree on the
dependent variable, and its failure, the variation atom, that two assignments agreeing on the
parameters differ on it. Widening the parameters weakens dependence and strengthens variation,
which is how the atoms compose into the constancy and variation conditions of
[degano-aloni-2025]. Teams are finite so that the atoms are decidable over a finite domain.

## References

* [hodges-1997]
* [vaananen-2007]
* [degano-aloni-2025]
-/

namespace Team

variable {V E : Type*}

/-- The dependence atom `dep(Z, u)`: assignments of the team agreeing on every variable of `Z`
agree on `u`; with `Z` empty, `u` is constant across the team. -/
def Dep (T : Finset (V → E)) (Z : Finset V) (u : V) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, (∀ z ∈ Z, i z = j z) → i u = j u

/-- The variation atom `var(Z, u)`: two assignments of the team agree on `Z` and differ on
`u`. -/
def Var (T : Finset (V → E)) (Z : Finset V) (u : V) : Prop :=
  ∃ i ∈ T, ∃ j ∈ T, (∀ z ∈ Z, i z = j z) ∧ i u ≠ j u

instance [DecidableEq E] (T : Finset (V → E)) (Z : Finset V) (u : V) : Decidable (Dep T Z u) :=
  inferInstanceAs (Decidable (∀ i ∈ T, ∀ j ∈ T, (∀ z ∈ Z, i z = j z) → i u = j u))

instance [DecidableEq E] (T : Finset (V → E)) (Z : Finset V) (u : V) : Decidable (Var T Z u) :=
  inferInstanceAs (Decidable (∃ i ∈ T, ∃ j ∈ T, (∀ z ∈ Z, i z = j z) ∧ i u ≠ j u))

/-- Variation is the failure of dependence. -/
theorem var_iff_not_dep (T : Finset (V → E)) (Z : Finset V) (u : V) :
    Var T Z u ↔ ¬ Dep T Z u :=
  ⟨λ ⟨i, hi, j, hj, hZ, hne⟩ hdep => hne (hdep i hi j hj hZ),
    λ h => by unfold Dep at h; push Not at h; exact h⟩

/-- Dependence on fewer parameters is dependence on more. -/
theorem Dep.mono {T : Finset (V → E)} {Z Z' : Finset V} {u : V} (hZ : Z ⊆ Z') (h : Dep T Z u) :
    Dep T Z' u :=
  λ i hi j hj hagree => h i hi j hj λ z hz => hagree z (hZ hz)

/-- Variation on more parameters is variation on fewer. -/
theorem Var.anti {T : Finset (V → E)} {Z Z' : Finset V} {u : V} (hZ : Z ⊆ Z') (h : Var T Z' u) :
    Var T Z u :=
  let ⟨i, hi, j, hj, hagree, hne⟩ := h
  ⟨i, hi, j, hj, λ z hz => hagree z (hZ hz), hne⟩

/-- Dependence excludes variation on the same parameters. -/
theorem Dep.not_var {T : Finset (V → E)} {Z : Finset V} {u : V} (h : Dep T Z u) : ¬ Var T Z u :=
  λ hv => (var_iff_not_dep T Z u).1 hv h

end Team
