module

public import Mathlib.Data.Finset.Card
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Conditionals.WillConditional
public import Linglib.Semantics.Modality.Selectional
public import Linglib.Semantics.Supervaluation
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Core.Data.Trivalent
public import Linglib.Logic.Duality
public import Linglib.Semantics.Presupposition.Defs

/-!
# Counterfactual conditionals: three theories

This file defines three theories of counterfactuals, all stated over the closest
antecedent-worlds of a similarity ordering. On the universal theory *if p, would q* is true when
every closest `p`-world is a `q`-world. On the selectional theory a selection function picks one
closest `p`-world and ties are resolved by supervaluation, so the counterfactual is true when
every closest `p`-world is a `q`-world, false when none is, and indeterminate otherwise. On the
homogeneity theory the universal assertion carries the presupposition that the closest
`p`-worlds agree on `q`. The three agree whenever the closest antecedent-worlds agree on the
consequent, and part under embedding.

## Main definitions

* `Counterfactual.selectionalCounterfactual`: the selectional counterfactual.
* `Counterfactual.homogeneityCounterfactual`: the homogeneity counterfactual.
* `Counterfactual.selectionalMight`: the selectional *might*.

## Main results

* `Counterfactual.eval_homogeneityCounterfactual`: unembedded, the homogeneity counterfactual
  evaluates to the selectional one.
* `Counterfactual.selectionalCounterfactual_eq_true_iff_forall_compatible`: the selectional
  counterfactual is the supervaluation over the completions of the ordering.

## References

* [S. Ramotowska, P. Marty, J. Romoli and P. Santorio, *Counterfactuals and quantificational force:
  Experimental evidence for selectional semantics* (2025)][ramotowska-marty-romoli-santorio-2025]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
* [K. von Fintel, *Bare Plurals, Bare Conditionals, and Only* (1997)][von-fintel-1997]
* [M. Križ, *Aspects of Homogeneity in the Semantics of Natural Language* (2015)][kriz-2015]
* [K. Fine, *Vagueness, Truth and Logic* (1975)][fine-1975]
* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
-/

@[expose] public section


namespace Conditional.Counterfactual

open Presupposition

section Theories

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W) (p q r : Set W)
  [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] [DecidablePred (· ∈ r)] (w : W)

/-! ### The selectional theory -/

/-- The selectional counterfactual, true when every closest `p`-world is a `q`-world, false when
every one is a `qᶜ`-world, and indeterminate otherwise. -/
def selectionalCounterfactual : Trivalent :=
  if w ∈ closestImp sim p q then .true
  else if w ∈ closestImp sim p qᶜ then .false
  else .indet

variable {sim p q w}

theorem selectionalCounterfactual_eq_true_iff :
    selectionalCounterfactual sim p q w = .true ↔ w ∈ closestImp sim p q := by
  unfold selectionalCounterfactual; split_ifs <;> simp_all

theorem selectionalCounterfactual_eq_false_iff :
    selectionalCounterfactual sim p q w = .false ↔
      w ∉ closestImp sim p q ∧ w ∈ closestImp sim p qᶜ := by
  unfold selectionalCounterfactual; split_ifs <;> simp_all

/-- The selectional counterfactual is super-truth (`Trivalent.dist`) over the closest worlds. -/
theorem selectionalCounterfactual_eq_dist :
    selectionalCounterfactual sim p q w =
      Trivalent.dist (sim.closestWorlds w (Finset.univ.filter (· ∈ p))) (· ∈ q) := by
  unfold selectionalCounterfactual Trivalent.dist
  simp only [mem_closestImp_iff_closestWorlds, Set.mem_compl_iff]
  split_ifs with h₁ h₂ h₃ <;> try rfl
  all_goals first | exact absurd h₂ (by simpa using h₃) | simp_all

variable (sim p q w)

/-- The selectional disjunction of *if p, q* and *if p, not q* is never false. -/
theorem cem_selectional :
    selectionalCounterfactual sim p q w ⊔ selectionalCounterfactual sim p qᶜ w ≠ .false := by
  simp only [selectionalCounterfactual, compl_compl]
  split_ifs <;> simp_all (config := { decide := true })

/-! ### The homogeneity theory

The homogeneity counterfactual is a partial proposition. Unembedded, its three-valued evaluation
is the selectional counterfactual, and the two theories part only under embedding, where
[ramotowska-marty-romoli-santorio-2025] test them. -/

omit [DecidableEq W] [Fintype W] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] in
/-- The homogeneity counterfactual, which asserts that every closest `p`-world is a `q`-world and
presupposes that the closest `p`-worlds agree on `q`. -/
def homogeneityCounterfactual : PartialProp W where
  presup w := w ∈ closestImp sim p q ∨ w ∈ closestImp sim p qᶜ
  assertion w := w ∈ closestImp sim p q

omit [DecidableEq W] [Fintype W] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] in
/-- The presupposition is symmetric in the consequent and its negation. -/
theorem presup_homogeneityCounterfactual_compl :
    (homogeneityCounterfactual sim p qᶜ).presup w ↔
      (homogeneityCounterfactual sim p q).presup w := by
  simp only [homogeneityCounterfactual, compl_compl, or_comm]

omit [DecidableEq W] [Fintype W] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] in
/-- Negating the consequent negates the assertion when the presupposition holds and some closest
`p`-world exists. -/
theorem assertion_homogeneityCounterfactual_compl
    (h_presup : (homogeneityCounterfactual sim p q).presup w)
    (h_nonvac : (sim.closest w p).Nonempty) :
    (homogeneityCounterfactual sim p qᶜ).assertion w ↔
      ¬ (homogeneityCounterfactual sim p q).assertion w := by
  obtain ⟨v, hv⟩ := h_nonvac
  refine ⟨fun hn hq ↦ hn hv (hq hv), fun hn ↦ h_presup.resolve_left hn⟩

/-- Unembedded, the homogeneity counterfactual evaluates to the selectional counterfactual. -/
theorem eval_homogeneityCounterfactual :
    (homogeneityCounterfactual sim p q).eval w = selectionalCounterfactual sim p q w := by
  by_cases h₁ : w ∈ closestImp sim p q <;> by_cases h₂ : w ∈ closestImp sim p qᶜ <;>
    simp [PartialProp.eval, homogeneityCounterfactual, selectionalCounterfactual, h₁, h₂]

/-! ### Supervaluation over the closest worlds

The selectional counterfactual is supervaluation ([fine-1975]) over the closest worlds, each
closest world being one resolution of the selection function's tie. -/

open Semantics.Supervaluation (SpecSpace superTrue)

/-- The selectional counterfactual is supervaluation over the closest worlds. -/
theorem selectional_as_supervaluation
    (hne : (sim.closestWorlds w (Finset.univ.filter (· ∈ p))).Nonempty) :
    selectionalCounterfactual sim p q w =
      superTrue (· ∈ q) ⟨sim.closestWorlds w (Finset.univ.filter (· ∈ p)), hne⟩ :=
  selectionalCounterfactual_eq_dist

/-! ### *Might* counterfactuals

[lewis-1973] defines *if p, might q* as *not (if p, would not q)*. Together with Conditional
Excluded Middle that definition makes *might* equivalent to *would*, which Lewis counts against a
semantics validating it. [stalnaker-1981] rejects the definition instead, reading *might* as a
possibility operator over the whole conditional. -/

/-- The selectional *might* holds when the selectional counterfactual is not false. -/
def selectionalMight : Prop := selectionalCounterfactual sim p q w ≠ .false

instance : Decidable (selectionalMight sim p q w) := inferInstanceAs (Decidable (_ ≠ _))

/-- The selectional *might* is weaker than *would*, since with mixed closest worlds *might*
holds while *would* is indeterminate. -/
theorem selectional_might_weaker :
    ∃ (sim : SimilarityOrdering (Fin 3)) (p q : Set (Fin 3)) (_ : DecidablePred (· ∈ p))
      (_ : DecidablePred (· ∈ q)) (w : Fin 3),
      selectionalMight sim p q w ∧ selectionalCounterfactual sim p q w = .indet :=
  ⟨.ofBool (fun _ a b ↦ a == b) (by decide) (by decide), {1, 2}, {1}, inferInstance,
    inferInstance, 0, by decide, by decide⟩

/-! ### Distribution

Distribution of a counterfactual over a disjunctive consequent fails for the universal theory,
which quantifies over every closest world, and holds for the selectional theory when there is at
most one closest world ([stalnaker-1981]). -/

/-- With at most one closest world, the selectional counterfactual distributes over a disjunctive
consequent. -/
theorem distribution_selectional (h_unique : (sim.closest w p).Subsingleton)
    (h : selectionalCounterfactual sim p (q ∪ r) w = .true) :
    selectionalCounterfactual sim p q w = .true ∨ selectionalCounterfactual sim p r w = .true := by
  simp only [selectionalCounterfactual_eq_true_iff, mem_closestImp] at h ⊢
  rcases h_unique.eq_empty_or_singleton with h0 | ⟨v, hv⟩
  · simp [h0]
  · simpa only [hv, Set.singleton_subset_iff, Set.mem_union] using h

/-- The conditional of the closest worlds does not distribute over a disjunctive consequent when
one closest world is a `q`-world and another an `r`-world. -/
theorem distribution_fails_universal :
    ∃ (sim : SimilarityOrdering (Fin 3)) (p q r : Set (Fin 3)) (w : Fin 3),
      w ∈ closestImp sim p (q ∪ r) ∧ w ∉ closestImp sim p q ∧ w ∉ closestImp sim p r :=
  ⟨.ofBool (fun _ a b ↦ a == b) (by decide) (by decide), {1, 2}, {1}, {2}, 0, by decide,
    by decide, by decide⟩

end Theories

/-! ### The selectional theory as supervaluation

[stalnaker-1981] supervaluates the [stalnaker-1968] selection conditional over the completions of
a similarity ordering. A conditional is true when every completion makes it true, false when
every one makes it false, and indeterminate otherwise, which for a single conditional on a
finite, strongly centered ordering is the selectional counterfactual. The disjunction that
`cem_selectional` shows is never false is weaker than Stalnaker's claim that Conditional
Excluded Middle is true on every completion. -/

section Supervaluation

variable {W : Type*} [DecidableEq W] [Fintype W] {sim : SimilarityOrdering W} {p q : Set W}
  [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] {w : W}

/-- The selectional counterfactual is true iff the selection conditional is true on every
completion. -/
theorem selectionalCounterfactual_eq_true_iff_forall_compatible (hc : sim.isCentered) :
    selectionalCounterfactual sim p q w = .true ↔
      ∀ s : SelectionFunction W, s.Compatible sim → w ∈ selectionConditional s p q :=
  selectionalCounterfactual_eq_true_iff.trans (mem_closestImp_iff_forall_compatible hc)

/-- The selectional counterfactual is false iff the selection conditional is false on every
completion. -/
theorem selectionalCounterfactual_eq_false_iff_forall_compatible (hc : sim.isCentered) :
    selectionalCounterfactual sim p q w = .false ↔
      ∀ s : SelectionFunction W, s.Compatible sim → w ∉ selectionConditional s p q := by
  rw [selectionalCounterfactual_eq_false_iff, mem_closestImp_iff_forall_compatible hc,
    mem_closestImp_iff_forall_compatible hc]
  obtain ⟨s₀, hs₀, -⟩ := SelectionFunction.exists_compatible (p := Set.univ) (w := w) hc
    (by rw [SimilarityOrdering.closest_eq_singleton_of_mem hc (Set.mem_univ w)]; rfl)
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

/-- Under the uniqueness assumption of [stalnaker-1981], at most one closest antecedent-world, any
compatible selection function decides the selectional counterfactual. -/
theorem selectionalCounterfactual_eq_ofBool {s : SelectionFunction W} (hs : s.Compatible sim)
    (hu : (sim.closest w p).Subsingleton) (hp : p.Nonempty) :
    selectionalCounterfactual sim p q w = Trivalent.ofBool (decide (s.sel w p ∈ q)) := by
  have h : sim.closest w p = {s.sel w p} := hu.eq_singleton_of_mem (hs.sel_mem_closest hp)
  by_cases hq : s.sel w p ∈ q <;> simp [selectionalCounterfactual, h, hq, Trivalent.ofBool]

end Supervaluation

/-! ### The selection conditional as a *will*-conditional

[cariani-santorio-2018] give *will* a selection-function semantics and form *will*-conditionals
by restricting its modal parameter to the antecedent. A selection conditional with a possible
antecedent is the *will*-conditional whose parameter is the whole space. For an impossible
antecedent the *will*-conditional is not vacuous, unlike the selection conditional. -/

/-- A selection conditional with a possible antecedent is the will-conditional over the
universe. -/
theorem mem_selectionConditional_iff_willConditional_univ {W : Type*}
    (s : Conditional.SelectionFunction W) {p q : Set W} {w : W} (hp : p.Nonempty) :
    w ∈ selectionConditional s p q ↔
      Conditional.WillConditional.willConditional s (· ∈ p) (· ∈ q) Set.univ w := by
  rw [mem_selectionConditional_of_nonempty s hp]
  simp [Conditional.WillConditional.willConditional, Conditional.WillConditional.restrict,
    Modality.Selectional.willSem]

/-- With two antecedent-worlds tied for closest, a compatible selection function makes *if p, q*
true while the conditional of the closest worlds does not ([lewis-1973], [stalnaker-1981]). -/
theorem stalnaker_lewis_would_diverge :
    ∃ (sim : SimilarityOrdering (Fin 3)) (s : SelectionFunction (Fin 3)), sim.isCentered ∧
      s.Compatible sim ∧ (0 : Fin 3) ∈ selectionConditional s {1, 2} {1} ∧
      (0 : Fin 3) ∉ closestImp sim {1, 2} {1} := by
  let sim : SimilarityOrdering (Fin 3) := .ofRank fun w v ↦ if w = v then 0 else 1
  have hc : sim.isCentered := fun w w' h ↦ by simp [sim, SimilarityOrdering.ofRank, h]
  obtain ⟨s, hs, hsel⟩ := SelectionFunction.exists_compatible (sim := sim) (w := 0)
    (p := {1, 2}) (v := 1) hc (by decide)
  refine ⟨sim, s, hc, hs, ?_, by decide⟩
  rw [mem_selectionConditional_of_nonempty _ ⟨1, by simp⟩, hsel]
  rfl

end Conditional.Counterfactual
