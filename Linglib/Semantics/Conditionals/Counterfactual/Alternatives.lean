module

public import Linglib.Semantics.Conditionals.Counterfactual
public import Linglib.Logic.Duality

/-!
# Counterfactuals over sets of antecedent propositions

This file defines counterfactuals whose antecedent denotes a set of propositions, such as the
disjuncts of a disjunctive antecedent or the antecedent's truthmakers. Such a counterfactual can
be read distributively, requiring the counterfactual of each proposition, which validates the
simplification of disjunctive antecedents, or collectively, quantifying over the closest worlds
of their union, which does not. The homogeneous reading is true when every proposition's
counterfactual holds, false when none does, and indeterminate otherwise.

## Main definitions

* `Counterfactual.would`: the counterfactual over the union of the propositions.
* `Counterfactual.Distributive`: the counterfactual of each proposition.
* `Counterfactual.homogeneity`: the all-or-nothing verdict over the propositions.

## References

* [L. Alonso-Ovalle, *Counterfactuals, correlatives, and disjunction* (2009)][alonso-ovalle-2009]
* [P. Santorio, *Alternatives and truthmakers in conditional semantics* (2018)][santorio-2018]
* [F. Cariani and S. Goldstein, *Conditional heresies* (2020)][cariani-goldstein-2020]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973]
-/

@[expose] public section


namespace Conditional.Counterfactual

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W)
  (S : List (Finset W)) (C : Set W) [DecidablePred (· ∈ C)] (w : W)

/-- The union of the propositions in `S`. -/
def disjunctiveClosure : Finset W := S.foldr (· ∪ ·) ∅

omit [Fintype W] in
@[simp] theorem mem_disjunctiveClosure {x : W} :
    x ∈ disjunctiveClosure S ↔ ∃ A ∈ S, x ∈ A := by
  induction S with
  | nil => simp [disjunctiveClosure]
  | cons A S ih =>
    rw [disjunctiveClosure, List.foldr_cons, Finset.mem_union, List.exists_mem_cons_iff]
    exact or_congr_right ih

/-- The counterfactual over `S` quantifies over the closest worlds of the union of its
propositions. -/
def would : Prop := w ∈ closestImp sim ↑(disjunctiveClosure S) C

/-- The distributive reading, on which the counterfactual holds of each proposition in `S`. -/
def Distributive : Prop := ∀ A ∈ S, w ∈ closestImp sim ↑A C

/-- The all-or-nothing verdict over `S`. -/
def homogeneity : Trivalent :=
  Trivalent.distList S fun A ↦ w ∈ closestImp sim ↑A C

instance : Decidable (would sim S C w) :=
  inferInstanceAs (Decidable (w ∈ closestImp sim _ C))

instance : Decidable (Distributive sim S C w) :=
  inferInstanceAs (Decidable (∀ A ∈ S, w ∈ closestImp sim ↑A C))

theorem distributive_iff_homogeneity_eq_true :
    Distributive sim S C w ↔ homogeneity sim S C w = .true := by
  unfold homogeneity Trivalent.distList
  by_cases h : ∀ A ∈ S, w ∈ closestImp sim ↑A C
  · rw [ite_eq_left h]; exact ⟨fun _ ↦ rfl, fun _ ↦ h⟩
  · rw [ite_eq_right h]
    refine ⟨fun h' ↦ (h h').elim, fun h' ↦ ?_⟩
    split_ifs at h'

/-- The verdict is false iff `S` is nonempty and no proposition's counterfactual holds. -/
theorem homogeneity_eq_false_iff :
    homogeneity sim S C w = .false ↔ S ≠ [] ∧ ∀ A ∈ S, w ∉ closestImp sim ↑A C :=
  Trivalent.distList_eq_false_iff _ _

omit [Fintype W] [DecidablePred (· ∈ C)] in
/-- On a single proposition the counterfactual quantifies over its closest worlds. -/
theorem would_singleton (A : Finset W) : would sim [A] C w ↔ w ∈ closestImp sim ↑A C := by
  simp only [would, disjunctiveClosure, List.foldr, Finset.union_empty]

end Conditional.Counterfactual
