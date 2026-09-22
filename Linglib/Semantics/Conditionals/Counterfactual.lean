import Mathlib.Data.Finset.Card
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Conditionals.WillConditional
import Linglib.Semantics.Modality.Selectional
import Linglib.Semantics.Supervaluation
import Linglib.Semantics.Conditionals.SelectionFunction
import Linglib.Core.Data.Trivalent
import Linglib.Logic.Duality

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
-/

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

-- ════════════════════════════════════════════════════
-- Bridge: Selectional Semantics as Supervaluation
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- Might Counterfactuals: Lewis vs Stalnaker
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- Distribution Principle
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- Single-Selection-Function Variant (Stalnaker 1968)
-- ════════════════════════════════════════════════════

/-! ## Single-Selection-Function Variant
[stalnaker-1968]

Stalnaker's original counterfactual analysis used a single Stalnakerian
selection function — picking THE closest A-world — without supervaluation
over ties. This is the same `Conditional.SelectionFunction` infrastructure that
[cariani-santorio-2018] reuse for *will* (see
`Semantics/Modality/Selectional.lean`); the mechanism is identical,
only the temporal/modal target differs.

The supervaluation variant (`selectionalCounterfactual` above) generalises
this to handle ties: each "legitimate" selection function corresponds to a
choice point, and we supervaluate over them. The bridge below shows that
when the supervaluation's closest-worlds set is the singleton chosen by a
selection function, the supervaluation analysis (`Trivalent`) reduces to the
single-function analysis (`Bool`) under `Trivalent.ofBool`. -/

/-- **Stalnaker's single-selection-function counterfactual** [stalnaker-1968].
    `A □→ B` is true at `w` iff `B` holds at `s(w, ‖A‖)`. The counterfactual
    reading is the `Conditional.selectionConditional` clause
    (shared substrate) supplied with a similarity-induced selection function;
    it is the *same* truth-condition as the indicative
    `Stalnaker.moodedConditional`, differing only in admissible `s`. -/
def stalnakerCounterfactual {W : Type*} (s : Conditional.SelectionFunction W)
    (A B : W → Prop) (w : W) : Prop :=
  Conditional.selectionConditional s A B w

instance stalnakerCounterfactual_decidable {W : Type*} (s : Conditional.SelectionFunction W)
    (A B : W → Prop) [DecidablePred B] (w : W) :
    Decidable (stalnakerCounterfactual s A B w) :=
  inferInstanceAs (Decidable (B _))

/-- **Bridge: Stalnaker = supervaluation when closest is a singleton.**

    When the supervaluation's closest-worlds set is the singleton
    `{s.sel w ‖A‖}`, the supervaluation analysis (`Trivalent`) reduces
    to the single-selection-function analysis (`Bool`) under
    `Trivalent.ofBool`. The supervaluation gap arises only with ties; once
    ties are resolved by the selection function, both analyses coincide. -/
theorem stalnaker_eq_selectional_singleton {W : Type*} [DecidableEq W] [Fintype W]
    (s : Conditional.SelectionFunction W) (sim : SimilarityOrdering W) (p q : Set W)
    [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] (w : W)
    (h_singleton : sim.closest w p = {s.sel w p}) :
    selectionalCounterfactual sim p q w =
      Trivalent.ofBool (decide (stalnakerCounterfactual s (· ∈ p) (· ∈ q) w)) := by
  unfold selectionalCounterfactual stalnakerCounterfactual Conditional.selectionConditional
  by_cases hq : s.sel w p ∈ q
  · simp [h_singleton, hq, Trivalent.ofBool]
  · simp [h_singleton, hq, Trivalent.ofBool]

/-! ## Bridge: Stalnaker counterfactual = will-conditional over the universe

[cariani-santorio-2018] §5.3.2 + §5.3.1 unify *will*, *would*,
will-conditionals, and Stalnaker counterfactuals under a single
`Conditional.SelectionFunction` substrate. Each operator differs only in its
modal parameter `f`:

- `willSem s A f w` — bare *will* with parameter `f`
- `willConditional s A B f w` — *will* with parameter `f ∩ ‖A‖`
- `stalnakerCounterfactual s A B w` — *would* with parameter `‖A‖`,
  i.e. the unrestricted parameter is the whole universe

The bridge below makes this explicit: a Stalnaker counterfactual is
exactly a will-conditional whose ambient parameter is `Set.univ`. The
*if*-clause then restricts the universe down to the antecedent's truth
set, recovering Stalnaker's `s(w, ‖A‖)`. -/

/-- **Stalnaker counterfactual = will-conditional over the universe.**

[cariani-santorio-2018] §5.3.2 + §5.3.1: when the modal parameter
of the will-conditional is taken to be `Set.univ`, the Kratzer
restriction `Set.univ ∩ ‖A‖ = ‖A‖` recovers Stalnaker's selection
target. The `stalnakerCounterfactual` and `willConditional`
truth-conditions thus coincide (`↔`).

This is the formal payoff of the unification: bare *will* (`willSem`),
will-conditionals (`willConditional`), Stalnaker counterfactuals, and
*would*-conditionals (`wouldConditional`) all derive from one
`Conditional.SelectionFunction` mechanism, differing only in which modal
parameter the tense morphology supplies. -/
theorem stalnakerCounterfactual_eq_willConditional_universe
    {W : Type*} (s : Conditional.SelectionFunction W) (A B : W → Prop) (w : W) :
    stalnakerCounterfactual s A B w ↔
    Conditional.WillConditional.willConditional
      s A B Set.univ w := by
  unfold stalnakerCounterfactual
    Conditional.selectionConditional
    Conditional.WillConditional.willConditional
    Conditional.WillConditional.restrict
    Modality.Selectional.willSem
  rw [Set.univ_inter]

/-- **Stalnaker counterfactual = would-conditional over the universe.**

The same identity restated in *would*-conditional terms, exercising
the morphological identity `wouldConditional = willConditional`. The
counterfactual is, on the C&S analysis, a past-tense (would-) form,
so the would-conditional reading is the more natural surface gloss. -/
theorem stalnakerCounterfactual_eq_wouldConditional_universe
    {W : Type*} (s : Conditional.SelectionFunction W) (A B : W → Prop) (w : W) :
    stalnakerCounterfactual s A B w ↔
    Conditional.WillConditional.wouldConditional
      s A B Set.univ w :=
  stalnakerCounterfactual_eq_willConditional_universe s A B w

/-- **Trivalent ↔ would-conditional bridge** [cariani-santorio-2018]
    §5.3.1 + §5.3.2: composing `stalnaker_eq_selectional_singleton`
    (Trivalent ↔ Bool stalnakerCounterfactual under singleton-closest) with
    `stalnakerCounterfactual_eq_wouldConditional_universe` (Bool ↔ Prop
    would-conditional under universe parameter) gives a direct bridge
    from the supervaluation-valued `selectionalCounterfactual` to the
    Prop-valued *would*-conditional of `WillConditional`.

    Under the same `h_singleton` hypothesis that resolves the Trivalent
    gap (the closest-worlds set is exactly Stalnaker's selected world),
    the supervaluation analysis lands at `.true` iff the would-conditional
    holds. The two layers — Trivalent supervaluation over `Finset` and Prop
    selection-function over `Set` — collapse to the same content. -/
theorem selectional_eq_wouldConditional_singleton_universe
    {W : Type*} [DecidableEq W] [Fintype W]
    (s : Conditional.SelectionFunction W) (sim : SimilarityOrdering W) (p q : Set W)
    [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] (w : W)
    (h_singleton : sim.closest w p = {s.sel w p}) :
    selectionalCounterfactual sim p q w = .true ↔
      Conditional.WillConditional.wouldConditional s (· ∈ p) (· ∈ q) Set.univ w := by
  rw [stalnaker_eq_selectional_singleton s sim p q w h_singleton,
    ← stalnakerCounterfactual_eq_wouldConditional_universe]
  by_cases h : stalnakerCounterfactual s (· ∈ p) (· ∈ q) w <;> simp [Trivalent.ofBool, h]

/-- A Stalnakerian selection function on `Fin 3` that prefers `1`
    whenever Centering does not force the centre. Used to witness the
    Stalnaker/Lewis would divergence below.

    `selFn w S` returns `w` if `w ∈ S` (Centering); otherwise returns
    `1` if `1 ∈ S`; otherwise picks the unique non-`w` element. -/
private noncomputable def divergeSel : Conditional.SelectionFunction (Fin 3) :=
  open Classical in
  { sel := fun w S => if w ∈ S then w
                      else if (1 : Fin 3) ∈ S then 1
                      else if (0 : Fin 3) ∈ S then 0
                      else 2
    inclusion := by
      intro w S hS
      by_cases hw : w ∈ S
      · simp [hw]
      · by_cases h1 : (1 : Fin 3) ∈ S
        · simp [hw, h1]
        · by_cases h0 : (0 : Fin 3) ∈ S
          · simp [hw, h1, h0]
          · simp [hw, h1, h0]
            obtain ⟨x, hx⟩ := hS
            match x, hx with
            | 0, hx => exact absurd hx h0
            | 1, hx => exact absurd hx h1
            | 2, hx => exact hx
    centering := by intro w S hw; simp [hw] }

/-- **Stalnaker–Lewis would divergence** [cariani-santorio-2018]
    §5.3.2 motivation: there exist a world model, a selection function,
    a similarity ordering, an antecedent `A` and a consequent `B` such
    that the *Stalnakerian would* (single-selection-function reading)
    is `true` while the *Lewisian would* (universal over closest
    A-worlds) is `false`.

    Construction: three worlds with everyone equally close (closer ≡
    true), antecedent `A = {1, 2}`, consequent `B = {1}`. The closest
    `A`-worlds are the whole of `A = {1, 2}`, and the
    universal `∀ w ∈ {1, 2}. B w` fails at `w = 2`. Stalnaker's
    selection (`divergeSel`) picks `1`, where `B` holds. The same
    structural source — single-valuedness of selection vs. universal
    quantification over a non-trivial closest set — drives the C&S
    *will* / `universalWill` split in
    `Modality.Selectional`. -/
theorem stalnaker_lewis_would_diverge :
    ∃ (sim : SimilarityOrdering (Fin 3)) (A B : Fin 3 → Prop)
      (_ : DecidablePred A) (_ : DecidablePred B) (w : Fin 3),
      stalnakerCounterfactual divergeSel A B w ∧
      w ∉ closestImp sim {v | A v} {v | B v} := by
  classical
  refine ⟨.ofBool (fun _ _ _ => true) (by decide) (by decide),
          fun w => w = 1 ∨ w = 2,
          fun w => w = 1,
          inferInstance, inferInstance,
          0, ?_, ?_⟩
  · have h0 : ¬ ((0 : Fin 3) ∈ {w : Fin 3 | w = 1 ∨ w = 2}) := by
      decide
    have h1 : (1 : Fin 3) ∈ {w : Fin 3 | w = 1 ∨ w = 2} := by
      decide
    have hsel : divergeSel.sel 0 {w : Fin 3 | w = 1 ∨ w = 2} = 1 := by
      unfold divergeSel
      simp [h0, h1]
    show (fun w : Fin 3 => w = 1) (divergeSel.sel 0 _)
    rw [hsel]
  · decide

end Conditional.Counterfactual
