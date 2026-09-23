module

public import Mathlib.Data.Finset.Card
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Conditionals.WillConditional
public import Linglib.Semantics.Modality.Selectional
public import Linglib.Semantics.Supervaluation
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Core.Data.Trivalent
public import Linglib.Logic.Duality

/-!
# Counterfactual conditionals: three theories

[ramotowska-marty-romoli-santorio-2025] compare three theories of counterfactuals, all stated
over the closest antecedent-worlds of a similarity ordering:

1. The universal theory ([lewis-1973], [kratzer-2012]): *if p, would q* is true iff every
   closest `p`-world is a `q`-world, the conditional `closestImp` of `Conditionals/Basic.lean`.
2. The selectional theory ([stalnaker-1968], with [stalnaker-1981]'s supervaluation over ties):
   a selection function picks one closest `p`-world (`selectionalCounterfactual`), true when
   every closest `p`-world is a `q`-world, false when none is, indeterminate otherwise.
3. The homogeneity theory ([von-fintel-1997], [kriz-2015]): the universal assertion with the
   presupposition that the closest `p`-worlds agree on `q` (`homogeneityCounterfactual`).

The three agree whenever the closest antecedent-worlds agree on the consequent; their
predictions under quantifiers are derived in `Studies/RamotowskaEtAl2025.lean`.

## References

* [ramotowska-marty-romoli-santorio-2025]
* [lewis-1973]
* [kratzer-2012]
* [stalnaker-1968]
* [stalnaker-1981]
* [von-fintel-1997]
* [kriz-2015]
* [fine-1975]
* [cariani-santorio-2018]
-/

@[expose] public section


namespace Conditional.Counterfactual

section Theories

variable {W : Type*} [DecidableEq W] [Fintype W] (sim : SimilarityOrdering W) (p q r : Set W)
  [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] [DecidablePred (· ∈ r)] (w : W)

/-! ## The selectional theory -/

/-- Selectional counterfactual semantics ([stalnaker-1981]'s supervaluation over the
selection functions the similarity ordering allows): true when every closest `p`-world is a
`q`-world, false when every one is a `qᶜ`-world, indeterminate otherwise. -/
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

/-- The selectional counterfactual is Fine super-truth (`Trivalent.dist`) over the closest
worlds. -/
theorem selectionalCounterfactual_eq_dist :
    selectionalCounterfactual sim p q w =
      Trivalent.dist (sim.closestWorlds w (Finset.univ.filter (· ∈ p))) (· ∈ q) := by
  unfold selectionalCounterfactual Trivalent.dist
  simp only [mem_closestImp_iff_closestWorlds, Set.mem_compl_iff]
  split_ifs with h₁ h₂ h₃ <;> try rfl
  all_goals first | exact absurd h₂ (by simpa using h₃) | simp_all

variable (sim p q w)

/-- Conditional Excluded Middle for the selectional theory: *if p, q* or *if p, not q* is never
false. -/
theorem cem_selectional :
    selectionalCounterfactual sim p q w ⊔ selectionalCounterfactual sim p qᶜ w ≠ .false := by
  simp only [selectionalCounterfactual, compl_compl]
  split_ifs <;> simp_all (config := { decide := true })

/-! ## The homogeneity theory -/

/-- Presupposition status. -/
inductive PresupStatus where
  | satisfied
  | failed
  deriving Repr, DecidableEq

/-- Result of evaluating a sentence with presuppositions. -/
structure PresupResult where
  presupposition : PresupStatus
  assertion : Option Bool
  deriving Repr, DecidableEq

/-- Homogeneity counterfactual semantics: the universal assertion, presupposing that the closest
`p`-worlds agree on `q`. -/
def homogeneityCounterfactual : PresupResult :=
  if w ∈ closestImp sim p q then ⟨.satisfied, some true⟩
  else if w ∈ closestImp sim p qᶜ then ⟨.satisfied, some false⟩
  else ⟨.failed, none⟩

/-- Homogeneity for `q` is homogeneity for `qᶜ`. -/
theorem presup_preserved_homogeneity
    (h : (homogeneityCounterfactual sim p q w).presupposition = .satisfied) :
    (homogeneityCounterfactual sim p qᶜ w).presupposition = .satisfied := by
  simp only [homogeneityCounterfactual, compl_compl] at *
  split_ifs at h ⊢ <;> rfl

/-- Negation swaps the assertion when some closest `p`-world exists and the presupposition holds. -/
theorem negation_swap_homogeneity_nonvacuous
    (h_presup : (homogeneityCounterfactual sim p q w).presupposition = .satisfied)
    (h_nonvac : (sim.closest w p).Nonempty) :
    (homogeneityCounterfactual sim p q w).assertion.map (!·) =
      (homogeneityCounterfactual sim p qᶜ w).assertion := by
  obtain ⟨v, hv⟩ := h_nonvac
  simp only [homogeneityCounterfactual, compl_compl] at *
  split_ifs at h_presup ⊢ with h₁ h₂ h₃ <;> first | rfl | simp_all
  exact absurd (h₁ hv) (h₂ hv)

/-! The selectional counterfactual is supervaluation ([fine-1975]) over the closest worlds:
each closest world is a specification point, a legitimate resolution of the selection
function's tie. -/

open Semantics.Supervaluation (SpecSpace superTrue)

/-- Selectional counterfactual = supervaluation over the closest worlds. -/
theorem selectional_as_supervaluation
    (hne : (sim.closestWorlds w (Finset.univ.filter (· ∈ p))).Nonempty) :
    selectionalCounterfactual sim p q w =
      superTrue (· ∈ q) ⟨sim.closestWorlds w (Finset.univ.filter (· ∈ p)), hne⟩ :=
  selectionalCounterfactual_eq_dist

/-!
## *Might* counterfactuals

[lewis-1973] defines *if p, might q* as *not (if p, would not q)* (`might`). Together with
Conditional Excluded Middle that definition makes *might* equivalent to *would*
(`mem_might_closestImp_iff_of_cem`), which Lewis counts against a semantics validating it;
[stalnaker-1981] rejects the definition instead, reading *might* as a possibility operator over
the whole conditional, true when the selectional conditional is not determinately false
(`selectionalMight`).
-/

/-- The selectional *might*: the selectional counterfactual is not determinately false. -/
def selectionalMight : Prop := selectionalCounterfactual sim p q w ≠ .false

instance : Decidable (selectionalMight sim p q w) := inferInstanceAs (Decidable (_ ≠ _))

/-- The selectional *might* is weaker than *would*: with mixed closest worlds, *might* holds while
*would* is indeterminate. -/
theorem selectional_might_weaker :
    ∃ (sim : SimilarityOrdering (Fin 3)) (p q : Set (Fin 3)) (_ : DecidablePred (· ∈ p))
      (_ : DecidablePred (· ∈ q)) (w : Fin 3),
      selectionalMight sim p q w ∧ selectionalCounterfactual sim p q w = .indet :=
  ⟨.ofBool (fun _ a b ↦ a == b) (by decide) (by decide), {1, 2}, {1}, inferInstance,
    inferInstance, 0, by decide, by decide⟩

/-!
## Distribution
[stalnaker-1981]

The distribution principle `(p □→ q ∪ r) ⊃ ((p □→ q) ∨ (p □→ r))` fails for the universal
theory, which quantifies over every closest world, but holds for the selectional theory when
there is at most one closest world.
-/

/-- Distribution holds for the selectional theory with at most one closest world. -/
theorem distribution_selectional (h_unique : (sim.closest w p).Subsingleton)
    (h : selectionalCounterfactual sim p (q ∪ r) w = .true) :
    selectionalCounterfactual sim p q w = .true ∨ selectionalCounterfactual sim p r w = .true := by
  simp only [selectionalCounterfactual_eq_true_iff, mem_closestImp] at h ⊢
  rcases h_unique.eq_empty_or_singleton with h0 | ⟨v, hv⟩
  · simp [h0]
  · simpa only [hv, Set.singleton_subset_iff, Set.mem_union] using h

/-- Distribution fails for the universal theory: two closest `p`-worlds, one a `q`-world and
the other an `r`-world. -/
theorem distribution_fails_universal :
    ∃ (sim : SimilarityOrdering (Fin 3)) (p q r : Set (Fin 3)) (w : Fin 3),
      w ∈ closestImp sim p (q ∪ r) ∧ w ∉ closestImp sim p q ∧ w ∉ closestImp sim p r :=
  ⟨.ofBool (fun _ a b ↦ a == b) (by decide) (by decide), {1, 2}, {1}, {2}, 0, by decide,
    by decide, by decide⟩

end Theories

/-! ## The selectional theory as supervaluation

[stalnaker-1981] supervaluates the [stalnaker-1968] selection conditional over the completions of
a similarity ordering, each yielding the selection function that picks its least
antecedent-world (`SelectionFunction.Compatible`): a conditional is true when every completion
makes it true, false when every one makes it false, and indeterminate otherwise. For a single
conditional on a finite, strongly centered ordering that is `selectionalCounterfactual`; the
Kleene disjunction of `cem_selectional` is weaker than Stalnaker's claim that Conditional
Excluded Middle is true on every completion (`cem_superTrue`). -/

section Supervaluation

variable {W : Type*} [DecidableEq W] [Fintype W] {sim : SimilarityOrdering W} {p q : Set W}
  [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] {w : W}

/-- True: every compatible selection function makes the selection conditional true. -/
theorem selectionalCounterfactual_eq_true_iff_forall_compatible (hc : sim.isCentered) :
    selectionalCounterfactual sim p q w = .true ↔
      ∀ s : SelectionFunction W, s.Compatible sim → w ∈ selectionConditional s p q :=
  selectionalCounterfactual_eq_true_iff.trans (mem_closestImp_iff_forall_compatible hc)

/-- False: every compatible selection function makes the selection conditional false. -/
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

/-- Under [stalnaker-1981]'s uniqueness assumption, at most one closest antecedent-world, the
supervaluation is decided by any compatible selection function: the gap arises only with ties. -/
theorem selectionalCounterfactual_eq_ofBool {s : SelectionFunction W} (hs : s.Compatible sim)
    (hu : (sim.closest w p).Subsingleton) (hp : p.Nonempty) :
    selectionalCounterfactual sim p q w = Trivalent.ofBool (decide (s.sel w p ∈ q)) := by
  have h : sim.closest w p = {s.sel w p} := hu.eq_singleton_of_mem (hs.sel_mem_closest hp)
  by_cases hq : s.sel w p ∈ q <;> simp [selectionalCounterfactual, h, hq, Trivalent.ofBool]

end Supervaluation

/-! ## Bridge: the selection conditional is the *will*-conditional over the universe

[cariani-santorio-2018] give *will* a selection-function semantics, *will*-conditionals by
restricting its modal parameter to the antecedent, and a Stalnakerian *would* the same meaning up
to the modal base. A selection conditional with a possible antecedent is the will-conditional
whose parameter is the whole space; for an impossible antecedent the will-conditional is not
vacuous, unlike [stalnaker-1968]'s. -/

/-- A selection conditional with a possible antecedent is the will-conditional over the
universe. -/
theorem mem_selectionConditional_iff_willConditional_univ {W : Type*}
    (s : Conditional.SelectionFunction W) {p q : Set W} {w : W} (hp : p.Nonempty) :
    w ∈ selectionConditional s p q ↔
      Conditional.WillConditional.willConditional s (· ∈ p) (· ∈ q) Set.univ w := by
  rw [mem_selectionConditional_of_nonempty s hp]
  simp [Conditional.WillConditional.willConditional, Conditional.WillConditional.restrict,
    Modality.Selectional.willSem]

/-- **Selection versus supervaluation** ([lewis-1973], [stalnaker-1981]): with two antecedent-worlds
tied for closest, a selection function compatible with the ordering makes *if p, q* true while the
supervaluation, the conditional of the closest worlds, does not. -/
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
