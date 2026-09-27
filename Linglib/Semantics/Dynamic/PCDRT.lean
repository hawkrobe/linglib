module

public import Linglib.Semantics.Dynamic.CDRT
public import Linglib.Logic.Assignment
public import Mathlib.Logic.Relator

/-!
# Plural CDRT

Compositional DRT over plural information states ([van-den-berg-1996], [brasoveanu-2007],
[brasoveanu-2010]). An information state is a set of CDRT states, a matrix whose rows are
assignments and whose columns are drefs: a dref stores the set of its values in the rows, and the
rows store the dependencies between the values of different drefs. A dref takes the dummy value ★
in the rows where it has none; here its register holds an `Option E` and ★ is `none`.

Every CDRT update lifts to plural states cumulatively, each input row having a successor among
the output rows and each output row a predecessor among the input rows. This is how dref
introduction `[u]` lifts to plural states, and the lift is a functor. Atomic conditions hold
distributively of the rows where their drefs have values. Structured inclusion selects a subset
of a dref's values by discarding rows, so the subset keeps exactly the superset's dependencies.
A dref's values and its cells are the operators `sumDref` and `restrict` of `PluralAssign`.

## Main definitions

* `Update.cumul`: the cumulative lift of an update to plural states.
* `PCDRT.value`, `PCDRT.cell`, `PCDRT.dep`: a dref's values, the rows where it has a given
  one, and the pairs of values two drefs have in a row.
* `PCDRT.intro`: dref introduction `[u]`.
* `PCDRT.atom`, `PCDRT.atom₂`, `PCDRT.sing`: distributive predication and singular number.
* `PCDRT.structSub`, `PCDRT.structSubAll`: structured inclusion.

## Main results

* `Update.cumul_id`, `Update.cumul_comp`: the lift is a functor.
* `Update.mem_cumul_iff_biTotal`: the lift relates two states exactly when the update is
  bitotal between their rows.
* `Update.cumul_test`: a lifted test checks every row.
* `PCDRT.value_eq_of_fixes`: a dref an update fixes keeps its values under the lifted update.
* `PCDRT.dep_subset_of_structSub`, `PCDRT.dep_eq_of_structSubAll`: a structured subset keeps
  only, and with the full condition all, of the superset's dependencies.

## References

* [van-den-berg-1996]
* [brasoveanu-2007]
* [brasoveanu-2010]
* [haug-dalrymple-2020]
* [spector-2025]
-/

@[expose] public section

namespace DynamicSemantics.Update

open SetRel

variable {S : Type*} {D D₁ D₂ : Update S} {I J : Set S}

/-- The cumulative lift of an update to plural states ([brasoveanu-2010] (18)): every input
row has a `D`-successor among the output rows, and every output row a `D`-predecessor among the
input rows. -/
def cumul (D : Update S) : Update (Set S) :=
  {(I, J) | (∀ i ∈ I, ∃ j ∈ J, i ~[D] j) ∧ ∀ j ∈ J, ∃ i ∈ I, i ~[D] j}

theorem mem_cumul_iff_subset : I ~[cumul D] J ↔ I ⊆ D.preimage J ∧ J ⊆ D.image I :=
  Iff.rfl

/-- The lift relates `I` to `J` when `D` restricted to their rows is bitotal. -/
theorem mem_cumul_iff_biTotal :
    I ~[cumul D] J ↔ Relator.BiTotal fun (i : I) (j : J) ↦ i.1 ~[D] j.1 := by
  simp [cumul, Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal]

theorem cumul_id : cumul (SetRel.id : Update S) = SetRel.id := by
  ext ⟨I, J⟩
  refine ⟨fun ⟨h₁, h₂⟩ ↦ Set.Subset.antisymm (fun i hi ↦ ?_) (fun j hj ↦ ?_), ?_⟩
  · obtain ⟨j, hj, rfl⟩ := h₁ i hi
    exact hj
  · obtain ⟨i, hi, rfl⟩ := h₂ j hj
    exact hi
  · rintro (rfl : I = J)
    exact ⟨fun i hi ↦ ⟨i, hi, rfl⟩, fun j hj ↦ ⟨j, hj, rfl⟩⟩

/-- The lift preserves sequencing: a path through the intermediate rows gives the intermediate
state. -/
theorem cumul_comp (D₁ D₂ : Update S) : cumul (D₁ ○ D₂) = cumul D₁ ○ cumul D₂ := by
  ext ⟨I, J⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨{k | ∃ i ∈ I, ∃ j ∈ J, i ~[D₁] k ∧ k ~[D₂] j}, ⟨fun i hi ↦ ?_, ?_⟩, ?_, ?_⟩
    · obtain ⟨j, hj, k, hik, hkj⟩ := h₁ i hi
      exact ⟨k, ⟨i, hi, j, hj, hik, hkj⟩, hik⟩
    · rintro k ⟨i, hi, _, _, hik, _⟩
      exact ⟨i, hi, hik⟩
    · rintro k ⟨_, _, j, hj, _, hkj⟩
      exact ⟨j, hj, hkj⟩
    · intro j hj
      obtain ⟨i, hi, k, hik, hkj⟩ := h₂ j hj
      exact ⟨k, ⟨i, hi, j, hj, hik, hkj⟩, hkj⟩
  · rintro ⟨K, ⟨hIK, hKI⟩, hKJ, hJK⟩
    refine ⟨fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · obtain ⟨k, hk, hik⟩ := hIK i hi
      obtain ⟨j, hj, hkj⟩ := hKJ k hk
      exact ⟨j, hj, k, hik, hkj⟩
    · obtain ⟨k, hk, hkj⟩ := hJK j hj
      obtain ⟨i, hi, hik⟩ := hKI k hk
      exact ⟨i, hi, k, hik, hkj⟩

theorem cumul_mono (h : D₁ ⊆ D₂) : cumul D₁ ⊆ cumul D₂ := by
  rintro ⟨I, J⟩ ⟨h₁, h₂⟩
  exact ⟨fun i hi ↦ (h₁ i hi).imp fun _ ⟨hj, hD⟩ ↦ ⟨hj, h hD⟩,
    fun j hj ↦ (h₂ j hj).imp fun _ ⟨hi, hD⟩ ↦ ⟨hi, h hD⟩⟩

/-- A lifted test checks its condition at every row ([brasoveanu-2010] (22)). -/
theorem cumul_test (C : Condition S) : cumul (test C) = test {I | I ⊆ C} := by
  ext ⟨I, J⟩
  simp only [cumul, test, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hIJ : I ⊆ J := fun i hi ↦ by obtain ⟨j, hj, rfl, -⟩ := h₁ i hi; exact hj
    have hJI : J ⊆ I := fun j hj ↦ by obtain ⟨i, hi, rfl, -⟩ := h₂ j hj; exact hi
    refine ⟨Set.Subset.antisymm hIJ hJI, fun i hi ↦ ?_⟩
    obtain ⟨j, -, rfl, hC⟩ := h₁ i (hJI hi)
    exact hC
  · rintro ⟨rfl, hC⟩
    exact ⟨fun i hi ↦ ⟨i, hi, rfl, hC hi⟩, fun j hj ↦ ⟨j, hj, rfl, hC hj⟩⟩

end DynamicSemantics.Update

namespace PCDRT

open DynamicSemantics DynamicSemantics.Update SetRel

variable {R S E : Type*} [RegisterStructure R S (Option E)] {u u' v : R} {I J : Set S}

/-! ### Values, rows and cells -/

/-- The values of `u` in `I`, `uI` ([brasoveanu-2010] (16), (38)); ★ is not a value. -/
def value (u : R) (I : Set S) : Set E := {x | ∃ i ∈ I, RegisterStructure.val u i = some x}

/-- The rows of `I` where `u` has the value `x`, `I_{u=x}` ((71)). -/
def cell (u : R) (x : E) (I : Set S) : Set S := {i ∈ I | RegisterStructure.val u i = some x}

/-- The dependency between `u` and `v` that `I` stores: the pairs of their values in a row. -/
def dep (u v : R) (I : Set S) : Set (E × E) :=
  {p | ∃ i ∈ I, RegisterStructure.val u i = some p.1 ∧ RegisterStructure.val v i = some p.2}

theorem value_singleton_of_eq {i : S} {x : E} (h : RegisterStructure.val u i = some x) :
    value u {i} = {x} := by
  ext y
  simp only [value, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, h,
    Option.some.injEq]
  exact eq_comm

theorem dep_singleton_of_eq {i : S} {x y : E} (hu : RegisterStructure.val u i = some x)
    (hv : RegisterStructure.val v i = some y) : dep u v {i} = {(x, y)} := by
  ext ⟨a, b⟩
  simp only [dep, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, hu, hv,
    Option.some.injEq, Prod.mk.injEq]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁.symm, h₂.symm⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁.symm, h₂.symm⟩⟩

theorem fst_mem_value_of_mem_dep {p : E × E} (h : p ∈ dep u v I) : p.1 ∈ value u I :=
  let ⟨i, hi, hu, _⟩ := h; ⟨i, hi, hu⟩

theorem snd_mem_value_of_mem_dep {p : E × E} (h : p ∈ dep u v I) : p.2 ∈ value v I :=
  let ⟨i, hi, _, hv⟩ := h; ⟨i, hi, hv⟩

theorem value_mono (h : I ⊆ J) : value u I ⊆ value u J :=
  fun _ ⟨i, hi, hx⟩ ↦ ⟨i, h hi, hx⟩

/-- On plural partial assignments, the values of a dref are [haug-dalrymple-2020]'s `∪u`. -/
theorem value_eq_sumDref {Var D : Type*} [DecidableEq Var] (G : PluralAssign Var D) (x : Var) :
    value x G = G.sumDref x :=
  rfl

/-- On plural partial assignments, a cell is [spector-2025]'s restriction `G_{x=a}`. -/
theorem cell_eq_restrict {Var D : Type*} [DecidableEq Var] (G : PluralAssign Var D) (x : Var)
    (a : D) : cell x a G = G.restrict x a :=
  rfl

/-! ### Dref introduction and conditions -/

/-- Dref introduction `[u]` ([brasoveanu-2010] (18)): the cumulative lift of CDRT's random
assignment. -/
def intro (u : R) : Update (Set S) := cumul (randomAssign u)

/-- Introducing `u` at a one-row state can give it any value. -/
theorem singleton_mem_intro (i : S) (u : R) (e : Option E) :
    {i} ~[intro u] {RegisterStructure.extend i u e} :=
  ⟨fun _ hi ↦ ⟨_, rfl, e, by rw [hi]⟩, fun _ hj ↦ ⟨i, rfl, e, by rw [hj]⟩⟩

/-- The lift of an update that fixes `v` leaves `v`'s values alone. -/
theorem value_eq_of_fixes {D : Update S} (h : Fixes v D) (hIJ : I ~[cumul D] J) :
    value v J = value v I := by
  ext x
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨i, hi, hij⟩ := hIJ.2 j hj
    exact ⟨i, hi, (h i j hij) ▸ hx⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨j, hj, hij⟩ := hIJ.1 i hi
    exact ⟨j, hj, (h i j hij).symm ▸ hx⟩

/-- Introducing `u` leaves every other dref's values alone. -/
theorem value_intro_of_ne (h : v ≠ u) (hIJ : I ~[intro u] J) : value v J = value v I :=
  value_eq_of_fixes (fixes_randomAssign_of_ne h) hIJ

/-- A unary atomic condition `P{u}` ((30)): `u` has values, and all of them satisfy `P`. -/
def atom (P : E → Prop) (u : R) : Condition (Set S) :=
  {I | (value u I).Nonempty ∧ ∀ x ∈ value u I, P x}

/-- A binary atomic condition `P{u, v}` ((32)): some row values both drefs, and the values in
every such row are related by `P`. -/
def atom₂ (P : E → E → Prop) (u v : R) : Condition (Set S) :=
  {I | (dep u v I).Nonempty ∧ ∀ p ∈ dep u v I, P p.1 p.2}

/-- Singular number `sing(u)` ((39)): `u` has exactly one value. -/
def sing (u : R) : Condition (Set S) := {I | ∃ x, value u I = {x}}

/-! ### Structured inclusion -/

/-- Structured inclusion `u' ⋐ u` ((66)): in every row, `u'` has `u`'s value or ★. -/
def structSub (u' u : R) : Condition (Set S) :=
  {I | ∀ i ∈ I, RegisterStructure.val u' i = RegisterStructure.val u i ∨
    RegisterStructure.val u' i = none}

/-- Full structured inclusion `u' ⊑ u` ((68)): structured inclusion that also keeps every row
in which `u` has one of `u'`'s values. -/
def structSubAll (u' u : R) : Condition (Set S) :=
  {I | I ∈ structSub u' u ∧ ∀ i ∈ I, ∀ x ∈ value u' I,
    RegisterStructure.val u i = some x → RegisterStructure.val u' i = some x}

/-- A structured subset keeps only the superset's dependencies (p. 465): whatever `u'` is
paired with in a row, `u` is paired with there too. -/
theorem dep_subset_of_structSub (h : I ∈ structSub u' u) : dep u' v I ⊆ dep u v I := by
  rintro ⟨x, y⟩ ⟨i, hi, hx, hy⟩
  refine ⟨i, hi, ?_, hy⟩
  rcases h i hi with h' | h'
  · exact h' ▸ hx
  · simp [h'] at hx

/-- A fully structured subset keeps all of the superset's dependencies at its own values
(p. 466). -/
theorem dep_eq_of_structSubAll (h : I ∈ structSubAll u' u) :
    dep u' v I = {p ∈ dep u v I | p.1 ∈ value u' I} := by
  ext ⟨x, y⟩
  refine ⟨fun hp ↦ ⟨dep_subset_of_structSub h.1 hp, ?_⟩, ?_⟩
  · obtain ⟨i, hi, hx, -⟩ := hp
    exact ⟨i, hi, hx⟩
  · rintro ⟨⟨i, hi, hx, hy⟩, hxu'⟩
    exact ⟨i, hi, h.2 i hi x hxu' hx, hy⟩

end PCDRT
