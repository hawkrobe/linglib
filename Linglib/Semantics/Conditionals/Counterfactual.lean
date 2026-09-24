module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Core.Data.Trivalent
public import Linglib.Logic.Duality
public import Linglib.Semantics.Presupposition.Defs

/-!
# Counterfactual conditionals: three theories

This file defines three theories of counterfactuals, all stated over the closest
antecedent-worlds of a similarity ordering. On the universal theory of Lewis and Kratzer *if p,
would q* is true when every closest `p`-world is a `q`-world. On the selectional theory of
Stalnaker a selection function picks one closest `p`-world and ties are resolved by
supervaluation over the completions of the ordering, so the counterfactual is true when every
closest `p`-world is a `q`-world, false when none is, and indeterminate otherwise. On the
homogeneity theory of von Fintel and Križ the universal assertion carries the presupposition
that the closest `p`-worlds agree on `q`. The three agree whenever the closest antecedent-worlds
agree on the consequent, and part under embedding.

## Main definitions

* `Counterfactual.selectionalCounterfactual`: the selectional counterfactual, super-truth over
  the closest antecedent-worlds.
* `Counterfactual.superCounterfactual`: Stalnaker's supervaluation over completions.
* `Counterfactual.homogeneityCounterfactual`: the homogeneity counterfactual.
* `Counterfactual.selectionalMight`: the selectional *might*.

## Main results

* `Counterfactual.eval_homogeneityCounterfactual`: unembedded, the homogeneity counterfactual
  evaluates to the selectional one.
* `Counterfactual.superCounterfactual_eq_selectionalCounterfactual`: on a finite, strongly
  centered ordering the supervaluation over completions is the selectional counterfactual.

## References

* [S. Ramotowska, P. Marty, J. Romoli and P. Santorio, *Counterfactuals and quantificational force:
  Experimental evidence for selectional semantics* (2025)][ramotowska-marty-romoli-santorio-2025]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
* [K. von Fintel, *Bare Plurals, Bare Conditionals, and Only* (1997)][von-fintel-1997]
* [M. Križ, *Aspects of Homogeneity in the Semantics of Natural Language* (2015)][kriz-2015]
-/

@[expose] public section


namespace Conditional.Counterfactual

open Presupposition

section Theories

variable {W : Type*} (ord : W → Preorder W) (p q r : Set W) (w : W)

/-! ### The homogeneity theory

The homogeneity counterfactual is a partial proposition. Unembedded, its three-valued evaluation
is the selectional counterfactual, and the two theories part only under embedding, where
[ramotowska-marty-romoli-santorio-2025] test them. -/

/-- The homogeneity counterfactual, which asserts that every closest `p`-world is a `q`-world and
presupposes that the closest `p`-worlds agree on `q`. -/
def homogeneityCounterfactual : PartialProp W where
  presup w := w ∈ closestImp ord p q ∨ w ∈ closestImp ord p qᶜ
  assertion w := w ∈ closestImp ord p q

/-- The presupposition is symmetric in the consequent and its negation. -/
theorem presup_homogeneityCounterfactual_compl :
    (homogeneityCounterfactual ord p qᶜ).presup w ↔
      (homogeneityCounterfactual ord p q).presup w := by
  simp only [homogeneityCounterfactual, compl_compl, or_comm]

/-- Negating the consequent negates the assertion when the presupposition holds and some closest
`p`-world exists. -/
theorem assertion_homogeneityCounterfactual_compl
    (h_presup : (homogeneityCounterfactual ord p q).presup w)
    (h_nonvac : ((ord w).minimals p).Nonempty) :
    (homogeneityCounterfactual ord p qᶜ).assertion w ↔
      ¬ (homogeneityCounterfactual ord p q).assertion w := by
  obtain ⟨v, hv⟩ := h_nonvac
  refine ⟨fun hn hq ↦ hn hv (hq hv), fun hn ↦ h_presup.resolve_left hn⟩

/-! ### The selectional theory

The selectional counterfactual is super-truth over the closest antecedent-worlds, each of them
one resolution of the selection function's tie. -/

variable [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ p)]
  [DecidablePred (· ∈ q)] [DecidablePred (· ∈ r)]

/-- The selectional counterfactual, true when every closest `p`-world is a `q`-world, false when
every one is a `qᶜ`-world, and indeterminate otherwise. -/
def selectionalCounterfactual : Trivalent :=
  Trivalent.dist ((ord w).minimals p).toFinset (· ∈ q)

variable {ord p q w}

theorem selectionalCounterfactual_eq_true_iff :
    selectionalCounterfactual ord p q w = .true ↔ w ∈ closestImp ord p q := by
  simp [selectionalCounterfactual, Trivalent.dist_eq_true_iff, Set.subset_def]

theorem selectionalCounterfactual_eq_false_iff :
    selectionalCounterfactual ord p q w = .false ↔
      w ∉ closestImp ord p q ∧ w ∈ closestImp ord p qᶜ := by
  simp only [selectionalCounterfactual, Trivalent.dist_eq_false_iff, Set.toFinset_nonempty,
    Set.mem_toFinset, mem_closestImp, Set.subset_def, Set.mem_compl_iff]
  exact ⟨fun ⟨⟨v, hv⟩, h⟩ ↦ ⟨fun h' ↦ h v hv (h' v hv), h⟩, fun ⟨hn, h⟩ ↦
    ⟨Set.nonempty_iff_ne_empty.2 fun he ↦ hn fun v hv ↦ absurd hv (he ▸ Set.notMem_empty v), h⟩⟩

theorem selectionalCounterfactual_eq_indet_iff :
    selectionalCounterfactual ord p q w = .indet ↔
      w ∉ closestImp ord p q ∧ w ∉ closestImp ord p qᶜ := by
  simp [selectionalCounterfactual, Trivalent.dist_eq_indet_iff, Set.not_subset, and_comm]

/-- With closest antecedent-worlds, negating the consequent negates the verdict. -/
theorem selectionalCounterfactual_compl (h : ((ord w).minimals p).Nonempty) :
    selectionalCounterfactual ord p qᶜ w = (selectionalCounterfactual ord p q w).neg := by
  simpa [selectionalCounterfactual] using
    Trivalent.dist_not_of_nonempty _ (· ∈ q) (by simpa using h)

variable (ord p q w)

/-- The selectional disjunction of *if p, q* and *if p, not q* is never false. -/
theorem cem_selectional :
    selectionalCounterfactual ord p q w ⊔ selectionalCounterfactual ord p qᶜ w ≠ .false := by
  rcases ((ord w).minimals p).eq_empty_or_nonempty with h | h
  · simp [selectionalCounterfactual, h]
  · rw [selectionalCounterfactual_compl h]
    cases selectionalCounterfactual ord p q w <;> decide

/-- Unembedded, the homogeneity counterfactual evaluates to the selectional counterfactual. -/
theorem eval_homogeneityCounterfactual :
    (homogeneityCounterfactual ord p q).eval w = selectionalCounterfactual ord p q w := by
  by_cases h₁ : w ∈ closestImp ord p q <;> by_cases h₂ : w ∈ closestImp ord p qᶜ
  · simp [PartialProp.eval, homogeneityCounterfactual, h₁,
      selectionalCounterfactual_eq_true_iff.2 h₁]
  · simp [PartialProp.eval, homogeneityCounterfactual, h₁,
      selectionalCounterfactual_eq_true_iff.2 h₁]
  · simp [PartialProp.eval, homogeneityCounterfactual, h₁, h₂,
      selectionalCounterfactual_eq_false_iff.2 ⟨h₁, h₂⟩]
  · simp [PartialProp.eval, homogeneityCounterfactual, h₁, h₂,
      selectionalCounterfactual_eq_indet_iff.2 ⟨h₁, h₂⟩]

/-! ### *Might* counterfactuals

[lewis-1973] defines *if p, might q* as *not (if p, would not q)*. Together with Conditional
Excluded Middle that definition makes *might* equivalent to *would*, which Lewis counts against a
semantics validating it. [stalnaker-1981] rejects the definition instead, reading *might* as a
possibility operator over the whole conditional. -/

/-- The selectional *might* holds when the selectional counterfactual is not false. -/
def selectionalMight : Prop := selectionalCounterfactual ord p q w ≠ .false

instance : Decidable (selectionalMight ord p q w) := inferInstanceAs (Decidable (_ ≠ _))

/-- The selectional *might* is weaker than *would*, since with mixed closest worlds *might*
holds while *would* is indeterminate. -/
theorem selectional_might_weaker :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (_ : ∀ w, DecidableRel (ord w).le) (p q : Set (Fin 3))
      (_ : DecidablePred (· ∈ p)) (_ : DecidablePred (· ∈ q)) (w : Fin 3),
      selectionalMight ord p q w ∧ selectionalCounterfactual ord p q w = .indet :=
  ⟨fun _ ↦ ⊥, inferInstance, {1, 2}, {1}, inferInstance,
    inferInstance, 0, by decide, by decide⟩

/-! ### Distribution

Distribution of a counterfactual over a disjunctive consequent fails for the universal theory,
which quantifies over every closest world, and holds for the selectional theory when there is at
most one closest world ([stalnaker-1981]). -/

/-- With at most one closest world, the selectional counterfactual distributes over a disjunctive
consequent. -/
theorem distribution_selectional (h_unique : ((ord w).minimals p).Subsingleton)
    (h : selectionalCounterfactual ord p (q ∪ r) w = .true) :
    selectionalCounterfactual ord p q w = .true ∨ selectionalCounterfactual ord p r w = .true := by
  simp only [selectionalCounterfactual_eq_true_iff, mem_closestImp] at h ⊢
  rcases h_unique.eq_empty_or_singleton with h0 | ⟨v, hv⟩
  · simp [h0]
  · simpa only [hv, Set.singleton_subset_iff, Set.mem_union] using h

/-- The conditional of the closest worlds does not distribute over a disjunctive consequent when
one closest world is a `q`-world and another an `r`-world. -/
theorem distribution_fails_universal :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (p q r : Set (Fin 3)) (w : Fin 3),
      w ∈ closestImp ord p (q ∪ r) ∧ w ∉ closestImp ord p q ∧ w ∉ closestImp ord p r :=
  ⟨fun _ ↦ ⊥, {1, 2}, {1}, {2}, 0, by decide,
    by decide, by decide⟩

end Theories

/-! ### The selectional theory as supervaluation

[stalnaker-1981] supervaluates the [stalnaker-1968] selection conditional over the completions of
a similarity ordering. A conditional is true when every completion makes it true, false when
every one makes it false, and indeterminate otherwise (`superCounterfactual`), which for a single
conditional on a finite, strongly centered ordering is the selectional counterfactual. -/

section Supervaluation

variable {W : Type*} (ord : W → Preorder W) (p q : Set W) (w : W)

/-- The supervaluation of the selection conditional over the completions of a family of
preorders, true when every compatible selection function makes *if p, q* true, false when every
one makes it false, and indeterminate otherwise. -/
noncomputable def superCounterfactual : Trivalent :=
  open Classical in
  if ∀ s : SelectionFunction W, s.Compatible ord → w ∈ selectionConditional s p q then .true
  else if ∀ s : SelectionFunction W, s.Compatible ord → w ∉ selectionConditional s p q then .false
  else .indet

variable {ord p q w} [Fintype W] [∀ w, DecidableRel (ord w).le]
  [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)]

/-- The selectional counterfactual is true iff the selection conditional is true on every
completion. -/
theorem selectionalCounterfactual_eq_true_iff_forall_compatible (hc : IsCentered ord) :
    selectionalCounterfactual ord p q w = .true ↔
      ∀ s : SelectionFunction W, s.Compatible ord → w ∈ selectionConditional s p q :=
  selectionalCounterfactual_eq_true_iff.trans (mem_closestImp_iff_forall_compatible hc)

/-- The selectional counterfactual is false iff the selection conditional is false on every
completion. -/
theorem selectionalCounterfactual_eq_false_iff_forall_compatible (hc : IsCentered ord) :
    selectionalCounterfactual ord p q w = .false ↔
      ∀ s : SelectionFunction W, s.Compatible ord → w ∉ selectionConditional s p q := by
  rw [selectionalCounterfactual_eq_false_iff, mem_closestImp_iff_forall_compatible hc,
    mem_closestImp_iff_forall_compatible hc]
  obtain ⟨s₀, hs₀, -⟩ := SelectionFunction.exists_compatible (p := Set.univ) (w := w) hc
    ⟨Set.mem_univ w, fun u _ _ ↦ hc.le w u⟩
  constructor
  · rintro ⟨hn, hc'⟩ s hs hq
    rcases p.eq_empty_or_nonempty with rfl | hp
    · exact hn fun s _ ↦ by simp [mem_selectionConditional]
    · exact (mem_selectionConditional_of_nonempty s hp).1 (hc' s hs)
        ((mem_selectionConditional_of_nonempty s hp).1 hq)
  · intro h
    refine ⟨fun hall ↦ h s₀ hs₀ (hall s₀ hs₀), fun s hs ↦ ?_⟩
    rw [mem_selectionConditional]
    intro hp hq
    exact h s hs ((mem_selectionConditional_of_nonempty s hp).2 hq)

/-- On a finite, strongly centered family of preorders the supervaluation over completions is
the selectional counterfactual. -/
theorem superCounterfactual_eq_selectionalCounterfactual (hc : IsCentered ord) :
    superCounterfactual ord p q w = selectionalCounterfactual ord p q w := by
  unfold superCounterfactual
  rw [← selectionalCounterfactual_eq_true_iff_forall_compatible hc,
    ← selectionalCounterfactual_eq_false_iff_forall_compatible hc]
  cases selectionalCounterfactual ord p q w <;> simp

/-- Under the uniqueness assumption of [stalnaker-1981], at most one closest antecedent-world, any
compatible selection function decides the selectional counterfactual. -/
theorem selectionalCounterfactual_eq_ofBool {s : SelectionFunction W} (hs : s.Compatible ord)
    (hu : ((ord w).minimals p).Subsingleton) (hp : p.Nonempty) :
    selectionalCounterfactual ord p q w = Trivalent.ofBool (decide (s.sel w p ∈ q)) := by
  have h : (ord w).minimals p = {s.sel w p} := hu.eq_singleton_of_mem (hs.sel_mem_minimals hp)
  by_cases hq : s.sel w p ∈ q <;> simp [selectionalCounterfactual, h, hq, Trivalent.ofBool]

end Supervaluation

/-! ### Ties -/

/-- With two antecedent-worlds tied for closest, a compatible selection function makes *if p, q*
true while the conditional of the closest worlds does not ([lewis-1973], [stalnaker-1981]). -/
theorem stalnaker_lewis_would_diverge :
    ∃ (ord : Fin 3 → Preorder (Fin 3)) (s : SelectionFunction (Fin 3)), IsCentered ord ∧
      s.Compatible ord ∧ (0 : Fin 3) ∈ selectionConditional s {1, 2} {1} ∧
      (0 : Fin 3) ∉ closestImp ord {1, 2} {1} := by
  let ord : Fin 3 → Preorder (Fin 3) := fun w ↦ Preorder.lift fun v ↦ if w = v then 0 else 1
  have hc : IsCentered ord := fun w w' h ↦ by simp [ord, h]
  obtain ⟨s, hs, hsel⟩ := SelectionFunction.exists_compatible (ord := ord) (w := 0)
    (p := {1, 2}) (v := 1) hc (by decide)
  refine ⟨ord, s, hc, hs, ?_, by decide⟩
  rw [mem_selectionConditional_of_nonempty _ ⟨1, by simp⟩, hsel]
  rfl

end Conditional.Counterfactual
