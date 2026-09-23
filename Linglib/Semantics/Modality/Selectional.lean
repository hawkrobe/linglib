/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Selectional semantics for *will*

This file defines the selectional semantics of the future modal *will* due to Cariani and
Santorio, and proves its logic and its prediction about credence.

On this account *will* does not quantify over a modal base of historical alternatives. It
applies its prejacent at the single world that a Stalnaker selection function picks out of a
modal parameter `f`, so `will_f A` is true at `w` iff `A` is true at `s(w, f)`, where the
selection function `s` is supplied by context and `f` is the relevant set of historical
alternatives. Cariani and Santorio argue that an adequate theory of *will* must meet three
constraints. *Will* has modal character: it takes scope, interacts with negation and
quantifiers, and embeds under attitudes. *Will* is scopeless: in matrix uses `will ¬A` and
`¬ will A` are equivalent, which universal quantification over a non-trivial modal base cannot
deliver. And a sincere assertion of `will A` is licensed by ordinary, non-extreme credence in
`A`, where a universal reading collapses the credence to 0 or 1.

## Main declarations

* `willSem`: the selectional truth condition.
* `negation_swap`, `will_excluded_middle`, `unembedded_collapse`: scopelessness, excluded
  middle, and collapse to the prejacent on the modal parameter.
* `will_eq_A_on_modalParam`: as sets of worlds, `will A` and `A` agree on the modal parameter,
  the transparency from which the prediction about credence follows.
* `Valid2`, `Valid1`: truth at every index, and truth at the index of the context.
* `willHistorical`: *will* over the metaphysical modal base of
  `Semantics/Modality/HistoricalAlternatives.lean`.
* `universalWill`: the universal reading that serves as a foil.
* `cognitive_role`: under any credence concentrated on the modal parameter, the measure of
  `will A` is the measure of `A`.

## References

* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [C. Condoravdi, *Temporal Interpretation of Modals: Modals for the Present and for the Past*
  (2002)][condoravdi-2002]
-/

@[expose] public section


namespace Modality.Selectional

open _root_.Conditional (SelectionFunction)
open HistoricalAlternatives
open scoped ENNReal

variable {W : Type*}

/-! ### The selectional truth-condition -/

/-- `willSem s A f w` holds when the prejacent `A` holds at the world that `s` selects from the
modal parameter `f` at `w`. So *will A* at `w` says that `A` holds at the unique selected historical
alternative `s.sel w f`. -/
def willSem (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) : Prop :=
  A (s.sel w f)

@[simp] theorem willSem_def (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s A f w ↔ A (s.sel w f) := Iff.rfl

/-- `willSem` is decidable when its prejacent is. -/
instance willSem_decidable (s : SelectionFunction W) (A : W → Prop)
    [DecidablePred A] (f : Set W) (w : W) :
    Decidable (willSem s A f w) :=
  inferInstanceAs (Decidable (A _))

/-! ### Scopelessness, CEM, and unembedded collapse -/

/-- Under the selectional semantics *will* commutes with negation, `will ¬A ↔ ¬ will A` (Negation
Swap), by the single-valuedness of selection: the selected world either satisfies `A` or does
not. -/
theorem negation_swap (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s (fun w' ↦ ¬ A w') f w ↔ ¬ willSem s A f w :=
  Iff.rfl

/-- `will A ∨ will ¬A` holds at every point of evaluation (Will Excluded Middle), since the selected
world `s.sel w f` is a single world at which `A` is either true or false. It is the selectional
analogue of Conditional Excluded Middle for Stalnaker's conditional. -/
theorem will_excluded_middle (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s A f w ∨ willSem s (fun w' ↦ ¬ A w') f w :=
  em _

/-- When the evaluation world is itself in the modal parameter, Centering forces the selected world
to be `w`, so `will A` reduces to `A w`. This explains the apparent factivity of unembedded
*will*-claims when the speaker presupposes that the actual world is among the historical
alternatives. -/
theorem unembedded_collapse (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) (hw : w ∈ f) :
    willSem s A f w ↔ A w := by
  unfold willSem
  rw [s.centering w f hw]

/-! ### Content transparency

As propositions, `will A` and `A` may differ outside the modal parameter but agree on it
([cariani-santorio-2018] §8.1), the fact from which the prediction about credence follows. -/

/-- On the modal parameter `f`, `will A` and `A` have the same truth value at each world, a
pointwise consequence of Centering (content transparency). -/
theorem will_eq_A_on_modalParam (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) :
    ∀ w ∈ f, willSem s A f w ↔ A w :=
  fun w hw ↦ unembedded_collapse s A f w hw

/-- On `f`, `will (A ∧ B)` and `will A ∧ will B` coincide pointwise. -/
theorem will_and_eq_will_and_will_on_modalParam (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    ∀ w ∈ f, willSem s (fun w' ↦ A w' ∧ B w') f w ↔
              (willSem s A f w ∧ willSem s B f w) := by
  intro w _
  unfold willSem
  exact Iff.rfl

/-- On `f`, `will (A ∨ B)` and `will A ∨ will B` coincide pointwise. -/
theorem will_or_eq_will_or_will_on_modalParam (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    ∀ w ∈ f, willSem s (fun w' ↦ A w' ∨ B w') f w ↔
              (willSem s A f w ∨ willSem s B f w) := by
  intro w _
  unfold willSem
  exact Iff.rfl

/-- As propositions, `will A` and `A` coincide on the modal parameter `f`, the equality of truth
sets that underwrites `cognitive_role`. -/
theorem will_inter_modalParam_eq (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) :
    {w | willSem s A f w} ∩ f = {w | A w} ∩ f := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun ⟨h1, h2⟩ ↦ ⟨(unembedded_collapse s A f w h2).mp h1, h2⟩
  · exact fun ⟨h1, h2⟩ ↦ ⟨(unembedded_collapse s A f w h2).mpr h1, h2⟩

/-- On `f`, the truth set of `will (A ∧ B)` is the intersection of the truth sets of `will A` and
`will B`. It follows from the single-valuedness of selection, since at each world all three
propositions are evaluated at the same point `s.sel w f`. -/
theorem will_and_inter_modalParam_eq (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    {w | willSem s (fun w' ↦ A w' ∧ B w') f w} ∩ f =
      ({w | willSem s A f w} ∩ {w | willSem s B f w}) ∩ f := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun ⟨⟨hA, hB⟩, hw⟩ ↦ ⟨⟨hA, hB⟩, hw⟩
  · exact fun ⟨⟨hA, hB⟩, hw⟩ ↦ ⟨⟨hA, hB⟩, hw⟩

/-- On `f`, the truth set of `will (A ∨ B)` is the union of the truth sets of `will A` and
`will B`. -/
theorem will_or_union_modalParam_eq (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    {w | willSem s (fun w' ↦ A w' ∨ B w') f w} ∩ f =
      ({w | willSem s A f w} ∪ {w | willSem s B f w}) ∩ f := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · exact fun ⟨h, hw⟩ ↦ ⟨h, hw⟩
  · exact fun ⟨h, hw⟩ ↦ ⟨h, hw⟩

/-! ### Validity

[cariani-santorio-2018] §6 distinguish validity₁, truth at the index of the context of
utterance, from validity₂, truth at every index. -/

/-- A propositional schema is valid₂ when it holds at every triple of a selection function, a modal
parameter and a world. -/
def Valid2 (φ : SelectionFunction W → Set W → W → Prop) : Prop :=
  ∀ s f w, φ s f w

/-- A propositional schema is valid₁ at a context when it holds at the index the utterance fixes,
its selection function `sCtx`, modal parameter `fCtx` and world `wCtx`. A schema can be valid₁
at every context without being valid₂, and postsemantic indeterminacy lives in the gap. -/
@[reducible] def Valid1 (φ : SelectionFunction W → Set W → W → Prop)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) : Prop :=
  φ sCtx fCtx wCtx

/-- A schema that is valid₂ is valid₁ at every context, since a schema holding at every index holds
at the contextually determined one. The converse fails, and postsemantic indeterminacy is precisely
the gap between the two. -/
theorem valid2_implies_valid1 {φ : SelectionFunction W → Set W → W → Prop}
    (h : Valid2 φ) (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) :
    Valid1 φ sCtx fCtx wCtx :=
  h sCtx fCtx wCtx

/-- Negation Swap is valid₂. -/
theorem valid2_negation_swap (A : W → Prop) :
    Valid2 (W := W) fun s f w ↦
      willSem s (fun w' ↦ ¬ A w') f w ↔ ¬ willSem s A f w :=
  fun s f w ↦ negation_swap s A f w

/-- Will Excluded Middle is valid₂. -/
theorem valid2_will_excluded_middle (A : W → Prop) :
    Valid2 (W := W) fun s f w ↦
      willSem s A f w ∨ willSem s (fun w' ↦ ¬ A w') f w :=
  fun s f w ↦ will_excluded_middle s A f w

/-- The disjunction `will A ∨ will ¬A` holds at the context of utterance (Postsemantic Will Excluded
Middle), as the valid₁ specialization of `valid2_will_excluded_middle`. Under a single contextually
fixed selection function the postsemantic principle follows from the compositional one. -/
theorem postsemantic_will_excluded_middle (A : W → Prop)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) :
    Valid1 (W := W) (fun s f w ↦
      willSem s A f w ∨ willSem s (fun w' ↦ ¬ A w') f w)
      sCtx fCtx wCtx :=
  valid2_implies_valid1 (valid2_will_excluded_middle A) sCtx fCtx wCtx

/-! ### Historical alternatives

Selectional *will* over Condoravdi's metaphysical modal base, the historical alternatives of
`Semantics/Modality/HistoricalAlternatives.lean`. -/

/-- Selectional *will* over historical alternatives evaluates the prejacent at the world selected
from the metaphysical modal base at the world and time of evaluation. -/
def willHistorical {T : Type*} (s : SelectionFunction W)
    (history : HistoricalAlternatives W T) (A : W → Prop)
    (w : W) (t : T) : Prop :=
  willSem s A (metaphysicalBase history w t) w

/-- When the world-history relation is reflexive, the standard assumption that a world is among its
own historical alternatives, `willHistorical` collapses to its prejacent, so `will_t A` at `w`
reduces to `A w`. -/
theorem willHistorical_reflexive_collapse {T : Type*}
    (s : SelectionFunction W) {history : HistoricalAlternatives W T}
    (hRefl : history.reflexive) (A : W → Prop) (w : W) (t : T) :
    willHistorical s history A w t ↔ A w := by
  unfold willHistorical
  apply unembedded_collapse
  exact hRefl ⟨w, t⟩

/-! ### The universal foil

[cariani-santorio-2018] argue against the reading of *will* as universal quantification over the
modal parameter, on which credence in *will A* can only be 0 or 1 (§8.1). -/

/-- On the universal reading *will A* is true at `w` iff `A` holds at every world in the modal
parameter. The world `w` itself is not used, so universal *will* is independent of the index. -/
def universalWill (A : W → Prop) (f : Set W) (_w : W) : Prop :=
  ∀ w' ∈ f, A w'

/-- Negation Swap fails for universal *will*. When the modal parameter contains both an `A`-world
and a `¬A`-world, `∀A` is false and `∀¬A` is false too, so `¬∀A` and `∀¬A` differ in truth value. -/
theorem universal_negation_swap_fails {A : W → Prop} {f : Set W} {w : W}
    (h : ∃ w₁ ∈ f, ∃ w₂ ∈ f, A w₁ ∧ ¬ A w₂) :
    ¬ (universalWill (fun w' ↦ ¬ A w') f w ↔ ¬ universalWill A f w) := by
  obtain ⟨w₁, hw₁f, w₂, hw₂f, hA1, hnA2⟩ := h
  unfold universalWill
  intro hiff
  have hLHS_false : ¬ (∀ w' ∈ f, ¬ A w') :=
    fun hAll ↦ hAll w₁ hw₁f hA1
  have hRHS_true : ¬ (∀ w' ∈ f, A w') :=
    fun hAll ↦ hnA2 (hAll w₂ hw₂f)
  exact hLHS_false (hiff.mpr hRHS_true)

/-! ### Cognitive role

The selectional analysis predicts that credence in *will A* equals credence in `A` whenever the
credence is concentrated on the modal parameter ([cariani-santorio-2018] §8.1), which the
universal reading cannot deliver. Conjunctive, disjunctive and negated prejacents are instances
at `A ∩ B`, `A ∪ B` and `Aᶜ`. -/

/-- Under any credence `μ` concentrated on the modal parameter `f`, the measure of `will A`, the
worlds whose selected world is in `A`, equals the measure of `A`. An assertion of `will A` is
thus licensed by ordinary credence in `A`, where the universal reading forces the credence to be
`0` or `1`. -/
theorem cognitive_role [MeasurableSpace W] (s : SelectionFunction W) (A f : Set W)
    (μ : MeasureTheory.Measure W) (h_supp : μ fᶜ = 0) :
    μ {w | s.sel w f ∈ A} = μ A := by
  refine MeasureTheory.measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  have hf : ∀ᵐ w ∂μ, w ∈ f := h_supp
  filter_upwards [hf] with w hw
  rw [s.centering w f hw]

/-! ### Validity of arguments

[cariani-santorio-2018] §6 distinguishes Validity₁ (truth at the
context) from Validity₂ (truth at every index). Both notions extend
to multi-premise consequence: an argument `H₁, …, Hₙ ⊨ C` is valid₂
when every index that satisfies all premises also satisfies the
conclusion. -/

/-- An argument from premises to a conclusion is valid₂ when at every index at which all the
premises are true the conclusion is true too. -/
def Valid2Arg (premises : List (SelectionFunction W → Set W → W → Prop))
    (conclusion : SelectionFunction W → Set W → W → Prop) : Prop :=
  ∀ s f w, (∀ φ ∈ premises, φ s f w) → conclusion s f w

/-- An argument is valid₁ at a context when, at the contextually fixed index, the conclusion holds
if all the premises do. -/
@[reducible] def Valid1Arg
    (premises : List (SelectionFunction W → Set W → W → Prop))
    (conclusion : SelectionFunction W → Set W → W → Prop)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) : Prop :=
  (∀ φ ∈ premises, φ sCtx fCtx wCtx) → conclusion sCtx fCtx wCtx

/-- An argument that is valid₂ is valid₁ at the context of utterance. -/
theorem valid2Arg_implies_valid1Arg
    {premises : List (SelectionFunction W → Set W → W → Prop)}
    {conclusion : SelectionFunction W → Set W → W → Prop}
    (h : Valid2Arg premises conclusion)
    (sCtx : SelectionFunction W) (fCtx : Set W) (wCtx : W) :
    Valid1Arg premises conclusion sCtx fCtx wCtx :=
  h sCtx fCtx wCtx

/-- Modus ponens for selectional *will* is valid₂, so from `will A ↔ will B` and `will A` one may
conclude `will B`. -/
theorem valid2_will_modus_ponens (A B : W → Prop) :
    Valid2Arg (W := W)
      [fun s f w ↦ willSem s A f w ↔ willSem s B f w,
       fun s f w ↦ willSem s A f w]
      (fun s f w ↦ willSem s B f w) := by
  intro s f w hPrem
  have hIff : willSem s A f w ↔ willSem s B f w :=
    hPrem (fun s f w ↦ willSem s A f w ↔ willSem s B f w) (by simp)
  have hA : willSem s A f w :=
    hPrem (fun s f w ↦ willSem s A f w) (by simp)
  exact hIff.mp hA

/-! ### *Would*

[cariani-santorio-2018] note that on a Stalnakerian semantics for *would* the selectional
analysis vindicates the morphological connection between *will* and *would*: the two have the
same meaning up to the possibilities in the modal base, so `willSem` with a counterfactual
parameter is *would*, and every theorem about *will* applies to it. -/

end Modality.Selectional
