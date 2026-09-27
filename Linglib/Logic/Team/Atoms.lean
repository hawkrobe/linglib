module

public import Linglib.Core.Relation.FactorsThroughOn
public import Linglib.Logic.Team.Definability
public import Mathlib.Data.Set.Restrict

/-!
# Dependency atoms

This file defines the atoms of team semantics as team properties, alongside the connectives of
`Team/Operations.lean`. Each atom compares values read off the points of a team through two
maps `f` and `g`:

* the dependence atom `Team.dep f g` of [vaananen-2007]: on the team, `g` is a function of `f`;
* the inclusion atom `Team.incl f g` ([anttila-haggblom-yang-2024]): every value of `f` on the
  team is a value of `g` there.

A team of assignments reads a tuple of variables through `f`; a team of Kripke worlds reads a
tuple of propositional atoms through the valuation. So Väänänen's first-order atom `=(Z, u)`,
here `Team.Dep`, and the modal atoms of `Team/Dependence.lean` and `Team/Inclusion.lean` are
instances of the same properties, and their closure behaviour is proved once: dependence is
inherited by subteams, variation by superteams, and inclusion by unions, while dependence is
not union-closed and inclusion not downward-closed.

Widening the parameters of `Team.Dep` weakens dependence and strengthens variation, which is how
the atoms compose into the constancy and variation conditions of [degano-aloni-2025].

## Main definitions

* `Team.dep`, `Team.incl`: the atoms as team properties.
* `Team.Dep`, `Team.Var`: the first-order dependence atom over a team of assignments, and the
  variation atom of [degano-aloni-2025], its failure witnessed by two assignments.

## Main results

* `Team.isLowerSet_dep`, `Team.supClosed_incl`, `Team.isUpperSet_var`: closure of the atoms.
* `Team.not_supClosed_dep`, `Team.not_isLowerSet_incl`: the closure properties they break.
* `Team.dep_iff_exists`: the dependent variable is a function of the parameters on the team.
* `Team.Dep.trans`: dependence composes.

## References

* [hodges-1997] Hodges, Compositional semantics for a language of imperfect information
* [vaananen-2007] Väänänen, Dependence Logic: A New Approach to Independence Friendly Logic
* [anttila-haggblom-yang-2024] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [degano-aloni-2025] Degano and Aloni, How to be (non-)specific
-/

@[expose] public section

namespace Team

variable {α β γ : Type*}

/-! ### The atoms as team properties -/

/-- The dependence atom: on the team, `g` is a function of `f`. -/
def dep (f : α → β) (g : α → γ) : TeamProperty α := {T | Function.FactorsThroughOn g f T}

/-- The inclusion atom: every value of `f` on the team is a value of `g` on the team. -/
def incl (f g : α → β) : TeamProperty α := {T | ∀ a ∈ T, ∃ b ∈ T, f a = g b}

variable {f : α → β} {g : α → γ} {T T' : Finset α}

theorem mem_dep : T ∈ dep f g ↔ ∀ a ∈ T, ∀ b ∈ T, f a = f b → g a = g b :=
  ⟨fun h _ ha _ hb ↦ h ha hb, fun h _ _ ha hb ↦ h _ ha _ hb⟩

@[simp] theorem mem_incl {f g : α → β} : T ∈ incl f g ↔ ∀ a ∈ T, ∃ b ∈ T, f a = g b := Iff.rfl

instance [DecidableEq β] [DecidableEq γ] (T : Finset α) : Decidable (T ∈ dep f g) :=
  decidable_of_iff _ mem_dep.symm

instance [DecidableEq β] (f g : α → β) (T : Finset α) : Decidable (T ∈ incl f g) :=
  inferInstanceAs (Decidable (∀ a ∈ T, ∃ b ∈ T, _))

theorem isLowerSet_dep (f : α → β) (g : α → γ) : IsLowerSet (dep f g) :=
  fun _ _ hT h ↦ Function.FactorsThroughOn.mono h (Finset.coe_subset.2 hT)

theorem singleton_mem_dep (a : α) : {a} ∈ dep f g :=
  mem_dep.2 fun _ hx _ hy _ ↦ by rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]

theorem empty_mem_dep : ∅ ∈ dep f g := mem_dep.2 fun _ h ↦ absurd h (Finset.notMem_empty _)

theorem empty_mem_incl (f g : α → β) : ∅ ∈ incl f g := fun _ h ↦ absurd h (Finset.notMem_empty _)

theorem supClosed_incl [DecidableEq α] (f g : α → β) : SupClosed (incl f g) := by
  intro s hs t ht a ha
  rcases Finset.mem_union.1 ha with ha | ha
  · obtain ⟨b, hb, h⟩ := hs a ha
    exact ⟨b, Finset.mem_union_left t hb, h⟩
  · obtain ⟨b, hb, h⟩ := ht a ha
    exact ⟨b, Finset.mem_union_right s hb, h⟩

/-- Dependence is not union-closed: two points agreeing on `f` and differing on `g` each form a
team satisfying the atom, but their union does not. -/
theorem not_supClosed_dep [DecidableEq α] {a b : α} (hf : f a = f b) (hg : g a ≠ g b) :
    ¬ SupClosed (dep f g) := fun h ↦
  hg <| mem_dep.1 (h (singleton_mem_dep a) (singleton_mem_dep b)) a (by simp) b (by simp) hf

/-- Inclusion is not downward-closed: if `b` supplies the `g`-value both of its own `f`-value
and of `a`'s, but `a` does not supply its own, then `{a, b}` satisfies the atom and `{a}` does
not. -/
theorem not_isLowerSet_incl [DecidableEq α] {f g : α → β} {a b : α} (hab : f a = g b)
    (hb : f b = g b) (ha : f a ≠ g a) : ¬ IsLowerSet (incl f g) := by
  intro h
  have hpair : {a, b} ∈ incl f g := fun x hx ↦
    ⟨b, by simp, by rcases Finset.mem_insert.1 hx with rfl | hx <;> simp_all⟩
  have hsub : ({a} : Finset α) ⊆ {a, b} := by simp
  obtain ⟨w, hw, hax⟩ := h hsub hpair a (Finset.mem_singleton_self a)
  rw [Finset.mem_singleton.1 hw] at hax
  exact ha hax

/-! ### The first-order atoms -/

variable {V E : Type*} {T T' : Finset (V → E)} {Z Z' : Finset V} {u : V}

/-- The first-order dependence atom `=(Z, u)` over a team of assignments: the value of `u` is
a function of the values of the variables of `Z`; with `Z` empty, `u` is constant across the
team. -/
def Dep (T : Finset (V → E)) (Z : Finset V) (u : V) : Prop :=
  T ∈ dep (Z : Set V).domRestrict (· u)

/-- The variation atom `var(Z, u)` of [degano-aloni-2025]: two assignments of the team agree on
`Z` and differ on `u`. It is the failure of `=(Z, u)` (`Team.not_dep`), stated by its
witnesses. -/
def Var (T : Finset (V → E)) (Z : Finset V) (u : V) : Prop :=
  ∃ i ∈ T, ∃ j ∈ T, (∀ z ∈ Z, i z = j z) ∧ i u ≠ j u

private theorem domRestrict_eq_iff {i j : V → E} :
    (Z : Set V).domRestrict i = (Z : Set V).domRestrict j ↔ ∀ z ∈ Z, i z = j z :=
  Set.domRestrict_eq_domRestrict_iff

/-- Assignments of the team agreeing on every variable of `Z` agree on `u`. -/
theorem dep_iff : Dep T Z u ↔ ∀ i ∈ T, ∀ j ∈ T, (∀ z ∈ Z, i z = j z) → i u = j u := by
  simp only [Dep, mem_dep, domRestrict_eq_iff]

theorem var_iff : Var T Z u ↔ ∃ i ∈ T, ∃ j ∈ T, (∀ z ∈ Z, i z = j z) ∧ i u ≠ j u := Iff.rfl

instance [DecidableEq E] (T : Finset (V → E)) (Z : Finset V) (u : V) : Decidable (Dep T Z u) :=
  decidable_of_iff _ dep_iff.symm

instance [DecidableEq E] (T : Finset (V → E)) (Z : Finset V) (u : V) : Decidable (Var T Z u) :=
  inferInstanceAs (Decidable (∃ i ∈ T, ∃ j ∈ T, _))

/-- Functional dependence, existentially: on the team, the value of `u` is a function of the
values of the variables of `Z`. -/
theorem dep_iff_exists [Nonempty E] :
    Dep T Z u ↔ ∃ h : (Z → E) → E, ∀ i ∈ T, i u = h ((Z : Set V).domRestrict i) :=
  Function.factorsThroughOn_iff_exists_eqOn

/-- Variation is the failure of dependence. -/
@[simp] theorem not_dep : ¬ Dep T Z u ↔ Var T Z u := by
  simp only [dep_iff, Var, not_forall, exists_prop]

@[simp] theorem not_var : ¬ Var T Z u ↔ Dep T Z u := by rw [← not_dep, not_not]

/-- Dependence excludes variation on the same parameters. -/
theorem Dep.not_var (h : Dep T Z u) : ¬ Var T Z u := Team.not_var.2 h

/-- A parameter depends on the parameters. -/
theorem dep_of_mem (h : u ∈ Z) : Dep T Z u := dep_iff.2 fun _ _ _ _ hZ ↦ hZ u h

/-- Every dependence holds on a team of one assignment. -/
theorem dep_singleton (i : V → E) : Dep {i} Z u := singleton_mem_dep i

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
theorem Dep.subset (hT : T' ⊆ T) (h : Dep T Z u) : Dep T' Z u := isLowerSet_dep _ _ hT h

/-- Variation is inherited by superteams. -/
theorem Var.superset (hT : T ⊆ T') (h : Var T Z u) : Var T' Z u :=
  let ⟨i, hi, j, hj, hagree, hne⟩ := h
  ⟨i, hT hi, j, hT hj, hagree, hne⟩

theorem isUpperSet_var (Z : Finset V) (u : V) : IsUpperSet {T : Finset (V → E) | Var T Z u} :=
  fun _ _ hT h ↦ h.superset hT

end Team
