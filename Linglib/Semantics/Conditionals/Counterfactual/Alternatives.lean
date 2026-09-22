module

public import Linglib.Semantics.Conditionals.Counterfactual
public import Linglib.Logic.Duality

/-!
# Counterfactuals over sets of antecedent propositions

A conditional whose antecedent denotes a set of propositions `S` rather than a single one —
the disjuncts of a disjunctive antecedent ([alonso-ovalle-2009]) or the antecedent's
truthmakers ([santorio-2018]) — can be read distributively or collectively. `Distributive`
requires the counterfactual of each proposition in `S` ([alonso-ovalle-2009]'s universal
quantification over alternatives, the assertion of [santorio-2018]'s `DIST_π`) and so
validates Simplification of Disjunctive Antecedents by construction; `would` lets the modal
extract the disjunctive closure `⋁S` ([santorio-2018]), which is [lewis-1973]'s
counterfactual on the disjunction and does not. `homogeneity` is the all-or-nothing verdict —
`.true` when every proposition's counterfactual holds, `.false` when none does, `.indet`
otherwise — the presupposition of `DIST_π` and the trivalent conditional of
[cariani-goldstein-2020].
-/

@[expose] public section


namespace Conditional.Counterfactual

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W)
  (S : List (Finset W)) (C : Set W) [DecidablePred (· ∈ C)] (w : W)

/-- The disjunctive closure `⋁S`. -/
def disjunctiveClosure : Finset W := S.foldr (· ∪ ·) ∅

omit [Fintype W] in
@[simp] theorem mem_disjunctiveClosure {x : W} :
    x ∈ disjunctiveClosure S ↔ ∃ A ∈ S, x ∈ A := by
  induction S with
  | nil => simp [disjunctiveClosure]
  | cons A S ih =>
    rw [disjunctiveClosure, List.foldr_cons, Finset.mem_union, List.exists_mem_cons_iff]
    exact or_congr_right ih

/-- The modal over `S` quantifies over the closest worlds of its disjunctive closure. -/
def would : Prop := w ∈ closestImp sim ↑(disjunctiveClosure S) C

/-- The distributive reading: the counterfactual holds of each proposition in `S`. -/
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

/-- The verdict is `.false` iff `S` is nonempty and no proposition's counterfactual holds. -/
theorem homogeneity_eq_false_iff :
    homogeneity sim S C w = .false ↔ S ≠ [] ∧ ∀ A ∈ S, w ∉ closestImp sim ↑A C :=
  Trivalent.distList_eq_false_iff _ _

omit [Fintype W] [DecidablePred (· ∈ C)] in
/-- On a singleton the modal quantifies over the closest worlds of its one proposition. -/
theorem would_singleton (A : Finset W) : would sim [A] C w ↔ w ∈ closestImp sim ↑A C := by
  simp only [would, disjunctiveClosure, List.foldr, Finset.union_empty]

end Conditional.Counterfactual
