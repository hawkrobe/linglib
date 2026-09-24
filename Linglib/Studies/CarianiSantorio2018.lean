/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Core.Probability.UniformOn
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Tactic.DeriveFintype

/-!
# Cariani and Santorio 2018: *will* done better

This file formalizes the selectional semantics of the future modal *will* by Cariani and Santorio.
A selection function, in Stalnaker's sense, picks one world out of a set of worlds: a world of the
set when the set is nonempty, and the world of evaluation itself when that world is in the set.
The modal parameter of *will* is a set of worlds, the historical alternatives to the world of the
context. *Will A* is true at a world when the world selected from the modal parameter is an
*A*-world. An *if*-clause restricts the modal parameter to the antecedent-worlds.

The paper sets three constraints on an account of *will*. It must be modal, manipulating a world
parameter, as its WOLL morphology shared with *would*, its epistemic readings and modal
subordination show (§2.1). It must be scopeless, commuting with negation whether unembedded or
embedded (§2.2). And it must fit the cognitive role of will-claims: the content of a will-claim
can carry the non-extreme credence a rational agent has in its prejacent (§2.3, §8.1). Selection
meets all three. *Will* shifts the world at which its prejacent is evaluated; a single selected
world settles every prejacent and its negation; and under a credence concentrated on the modal
parameter the content of *will A* has the credence of *A*. Modal subordination, as in *If A, will
B. Will C*, is read by coindexing the second *will* with the restricted parameter, so both
prejacents are evaluated at the world selected from the parameter restricted to *A* (§5.3.1,
(24)).

The paper distinguishes validity₁, truth preservation at every context, from validity₂, truth
preservation at every index (§6). The two come apart exactly because the world of a context lies
in its modal parameter, where *will A* collapses to *A*.

In the Sports Fan model Cynthia will wear a Warriors cap, a Giants cap, or no cap, and an agent
gives each option credence 1/3. The selectional content of *Cynthia will wear a Warriors cap* has
credence 1/3, while its universal reading, strict necessity over the historical alternatives, is
false throughout and has credence 0. The content of *if Cynthia wears a cap, she will wear a
Warriors cap* has credence 1/3 or 2/3 depending on the selection function, never the conditional
probability 1/2, since no proposition over the model has probability 1/2, an instance of Hájek's
point that conditional probabilities outnumber unconditional ones.

## Main definitions

* `will`: selectional *will* over a modal parameter.
* `willIf`: *if A, will B*, selectional *will* over the parameter restricted to *A*.
* `Valid1`, `Valid2`: validity over contexts and over all indices.
* `W`, `histAlt`, `cynthiaSel`, `cynthiaCredence`: the Sports Fan model.

## Main results

* `will_compl`, `willIf_compl`: negation swap, unembedded and under an *if*-clause.
* `will_excluded_middle`, `willIf_excluded_middle`: excluded middle is valid₂.
* `valid1_materialImp_will`, `not_valid2_materialImp_will`: *will A* entails *A* at every
  context but not at every index.
* `will_eq_selectionConditional`: on a possible parameter *will* is the selection conditional.
* `measure_will`: a credence concentrated on the parameter gives *will A* the credence of *A*.
* `cynthia_credence_one_third`, `universal_will_credence_zero`: the cognitive-role contrast.
* `universal_willIf_cem_fails`: the universal reading refutes conditional excluded middle.
* `cap_conditional_credence`, `no_unconditional_one_half`: the cap-conditional has credence 2/3,
  and no proposition has the conditional probability 1/2.

## Implementation notes

* Propositions are `Set W` and `will` is a preimage, so its logic is the preimage lemmas.
* `will` and `selectionConditional` differ only at the empty parameter, where the selection
  conditional is vacuously true and `will` evaluates the junk selection. The paper's selection
  functions are total and its conditional principles are restricted to antecedents compatible
  with the modal base (§7).
* Section and equation numbers follow the accepted manuscript (Draft of November 2, 2015).

## TODO

* The paper recovers credence 1/2 for the cap-conditional by refining contents to pairs of a world
  and a selection function (§8.2); this refinement is not formalized.

## References

* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [A. Hajek, *Probabilities of Conditionals — Revisited* (1989)][hajek-1989]
-/

@[expose] public section

namespace CarianiSantorio2018

open Conditional MeasureTheory ProbabilityTheory

section General

variable {W : Type*} (s : SelectionFunction W) {f A B : Set W} {w : W}

/-! ### Selectional *will*

The clause for *will* is (16) of §5.2, and its collapse at the context is (18). -/

/-- *Will A* over the modal parameter `f` holds at the worlds whose selection from `f` is an
`A`-world. -/
def will (f A : Set W) : Set W := (s.sel · f) ⁻¹' A

@[simp] theorem mem_will : w ∈ will s f A ↔ s.sel w f ∈ A := Iff.rfl

/-- *Will* commutes with negation, which is Negation Swap (§7). -/
theorem will_compl : will s f Aᶜ = (will s f A)ᶜ := Set.preimage_compl

/-- At a world of the modal parameter, *will A* is true exactly when `A` is. -/
theorem mem_will_of_mem (hw : w ∈ f) : w ∈ will s f A ↔ w ∈ A := by
  rw [mem_will, s.centering w f hw]

/-- On the modal parameter, *will A* and `A` hold at the same worlds. -/
theorem will_inter_self : will s f A ∩ f = A ∩ f :=
  Set.ext fun _ ↦ and_congr_left (mem_will_of_mem s)

/-- On a possible modal parameter, *will A* is the selection conditional of [stalnaker-1968] with
the modal parameter as antecedent. -/
theorem will_eq_selectionConditional (hf : f.Nonempty) : will s f A = selectionConditional s f A :=
  Set.ext fun _ ↦ (mem_selectionConditional_of_nonempty s hf).symm

/-! ### Validity -/

/-- A sentence is valid₂ when it is true at every index, every world under every selection
function and modal parameter. -/
def Valid2 (φ : SelectionFunction W → Set W → Set W) : Prop := ∀ s f, φ s f = Set.univ

/-- A sentence is valid₁ when it is true at every context, an index whose world lies in the modal
parameter. -/
def Valid1 (φ : SelectionFunction W → Set W → Set W) : Prop := ∀ s f, f ⊆ φ s f

theorem Valid2.valid1 {φ : SelectionFunction W → Set W → Set W} (h : Valid2 φ) : Valid1 φ :=
  fun s f ↦ (h s f).symm ▸ Set.subset_univ f

/-- Will Excluded Middle is valid₂ (§7). -/
theorem will_excluded_middle : Valid2 fun s f ↦ will s f A ∪ will s f Aᶜ := fun s _ ↦ by
  simp only [will_compl, Set.union_compl_self]

/-- Every context at which *will A* is true verifies `A`. -/
theorem valid1_materialImp_will : Valid1 fun s f ↦ materialImp (will s f A) A :=
  fun s _ _ hw ↦ (mem_will_of_mem s hw).1

/-! ### *If*-clauses

An *if*-clause restricts the modal parameter of *will* to the antecedent-worlds, by rule (21) of
§5.3.1. -/

/-- *If A, will B* is *will B* over the modal parameter restricted to the `A`-worlds. -/
def willIf (f A B : Set W) : Set W := will s (f ∩ A) B

/-- *Will* commutes with negation under an *if*-clause, which is Negation Swap in conditionals
(§7). Since the *if*-clause only shifts the parameter, the narrow form, *if A, will not B* against
*if A, not will B*, and the wide form, against *not (if A, will B)*, are this one equation. -/
theorem willIf_compl : willIf s f A Bᶜ = (willIf s f A B)ᶜ := will_compl s

/-- Conditional Excluded Middle for will-conditionals is valid₂ (§7). -/
theorem willIf_excluded_middle : Valid2 fun s f ↦ willIf s f A B ∪ willIf s f A Bᶜ :=
  fun s f ↦ will_excluded_middle s (f ∩ A)

/-- When the restricted parameter is possible, *if A, will B* is the selection conditional with
the restricted parameter as antecedent. -/
theorem willIf_eq_selectionConditional (h : (f ∩ A).Nonempty) :
    willIf s f A B = selectionConditional s (f ∩ A) B :=
  will_eq_selectionConditional s h

/-! ### Cognitive role -/

/-- Under a credence concentrated on the modal parameter, the content of *will A* has the
credence of `A`. -/
theorem measure_will [MeasurableSpace W] (μ : Measure W) (h : μ fᶜ = 0) :
    μ (will s f A) = μ A :=
  measure_congr <| Filter.eventuallyEqSet_iff.2 <| by
    filter_upwards [(h : ∀ᵐ w ∂μ, w ∈ f)] with w hw using mem_will_of_mem s hw

end General

/-! ### The Sports Fan model -/

/-- The three worlds of the Sports Fan scenario (§2.3) are those in which Cynthia wears a Warriors
cap, a Giants cap, or no cap. -/
inductive W where
  | cw | cg | cn
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The historical alternatives contain every cap choice, nothing being settled at the time of
utterance. -/
def histAlt : Set W := {.cw, .cg, .cn}

/-- The proposition that Cynthia wears a Warriors cap. -/
def warriorsCap : Set W := {.cw}

instance : DecidablePred (· ∈ warriorsCap) := fun w ↦ decEq w .cw

/-- The proposition that Cynthia wears some cap, Warriors or Giants. -/
def wearsCap : Set W := {.cw, .cg}

instance : DecidablePred (· ∈ wearsCap) := fun w ↦
  inferInstanceAs (Decidable (w = .cw ∨ w ∈ ({.cg} : Set W)))

/-- The selection map returns `w` when `w ∈ A`, and otherwise the first world of `A` in the order
cw, cg, cn. -/
noncomputable def selFn (w : W) (A : Set W) : W :=
  open Classical in
  if w ∈ A then w else
  if (W.cw : W) ∈ A then .cw else
  if (W.cg : W) ∈ A then .cg else .cn

theorem selFn_inclusion (w : W) (A : Set W) (hA : A.Nonempty) : selFn w A ∈ A := by
  obtain ⟨x, hx⟩ := hA
  unfold selFn
  split_ifs <;> first | assumption | cases x <;> simp_all

theorem selFn_centering (w : W) (A : Set W) (hw : w ∈ A) : selFn w A = w := ite_eq_left hw

/-- Cynthia's selection function is `selFn`. -/
noncomputable def cynthiaSel : SelectionFunction W where
  sel := selFn
  inclusion := selFn_inclusion
  centering := selFn_centering

/-- *Cynthia will wear a Warriors cap* is true at the Warriors-cap world. -/
theorem cynthia_will_warriorsCap : W.cw ∈ will cynthiaSel histAlt warriorsCap :=
  (mem_will_of_mem cynthiaSel (by simp [histAlt])).2 rfl

/-- *Will A* does not valid₂-entail `A`: at the Warriors-cap world, with the no-cap world as the
only historical alternative, *Cynthia will wear no cap* is true and its prejacent false. -/
theorem not_valid2_materialImp_will :
    ¬ Valid2 fun s f ↦ materialImp (will s f {W.cn}) {W.cn} := fun h ↦ by
  have := Set.eq_univ_iff_forall.1 (h cynthiaSel {.cn}) .cw
    (cynthiaSel.inclusion _ _ (Set.singleton_nonempty _))
  simp at this

instance : MeasurableSpace W := ⊤

instance : MeasurableSingletonClass W := ⟨fun _ ↦ trivial⟩

/-- The agent's credence is uniform, each cap choice getting 1/3. -/
noncomputable def cynthiaCredence : Measure W := uniformOn Set.univ

/-- The agent's credence is concentrated on the historical alternatives. -/
theorem cynthiaCredence_histAlt_compl : cynthiaCredence histAltᶜ = 0 := by
  have : histAltᶜ = (∅ : Set W) := by ext w; cases w <;> simp [histAlt]
  rw [this, measure_empty]

private theorem cynthiaCredence_coe (S : Finset W) : cynthiaCredence.real S = S.card / 3 := by
  rw [cynthiaCredence, uniformOn_univ_real_coe_finset, show Fintype.card W = 3 from rfl,
    Nat.cast_ofNat]

/-- The credence in *Cynthia will wear a Warriors cap* is the credence 1/3 of its prejacent. -/
theorem cynthia_credence_one_third :
    cynthiaCredence.real (will cynthiaSel histAlt warriorsCap) = 1 / 3 := by
  rw [measureReal_def, measure_will cynthiaSel cynthiaCredence cynthiaCredence_histAlt_compl,
    ← measureReal_def, show warriorsCap = ↑({.cw} : Finset W) by simp [warriorsCap],
    cynthiaCredence_coe]
  norm_num

/-- On the universal reading, *will A* is true when `A` holds at every historical alternative
(§2.1, §2.3), the strict necessity over the historical alternatives. It is false throughout an
open future, so *Cynthia will wear a Warriors cap* has credence 0. -/
theorem universal_will_credence_zero :
    cynthiaCredence.real (strictImp (fun _ : W ↦ histAlt) Set.univ warriorsCap) = 0 := by
  have : strictImp (fun _ : W ↦ histAlt) Set.univ warriorsCap = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ h ↦ by
      simpa [warriorsCap] using h ⟨(show W.cg ∈ histAlt by simp [histAlt]), trivial⟩
  rw [this, measureReal_empty]

/-- The universal reading of *if Cynthia wears a cap, she will wear a Warriors cap* refutes
Conditional Excluded Middle, since the restricted parameter holds a Warriors-cap world and a
Giants-cap world. -/
theorem universal_willIf_cem_fails :
    W.cw ∉ strictImp (fun _ ↦ histAlt) wearsCap warriorsCap ∧
      W.cw ∉ strictImp (fun _ ↦ histAlt) wearsCap warriorsCapᶜ :=
  not_mem_ofDomain_and_compl (v := .cw) (v' := .cg)
    ⟨by simp [histAlt], by simp [wearsCap]⟩ ⟨by simp [histAlt], by simp [wearsCap]⟩
    (by simp [warriorsCap]) (by simp [warriorsCap])

/-! ### The cap-conditional

The cap-conditional is (31) of §8.2. -/

/-- Under Cynthia's selection function, *if Cynthia wears a cap, she will wear a Warriors cap* is
true at the Warriors-cap world and the no-cap world. -/
theorem willIf_wearsCap_warriorsCap :
    willIf cynthiaSel histAlt wearsCap warriorsCap = {.cw, .cn} := by
  ext w
  cases w <;> simp [willIf, cynthiaSel, selFn, histAlt, wearsCap, warriorsCap]

/-- The content of the cap-conditional has credence 2/3, the value footnote 32 derives when the
no-cap world selects the Warriors-cap world. -/
theorem cap_conditional_credence :
    cynthiaCredence.real (willIf cynthiaSel histAlt wearsCap warriorsCap) = 2 / 3 := by
  rw [willIf_wearsCap_warriorsCap, show ({.cw, .cn} : Set W) = ↑({.cw, .cn} : Finset W) by simp,
    cynthiaCredence_coe]
  norm_num

/-- The probability of a Warriors cap conditional on some cap is 1/2. -/
theorem cap_warriors_credence_one_half :
    cynthiaCredence.real wearsCap ≠ 0 ∧ cynthiaCredence[|wearsCap].real warriorsCap = 1 / 2 := by
  have hwears : cynthiaCredence.real wearsCap = 2 / 3 := by
    rw [show wearsCap = ↑({.cw, .cg} : Finset W) by simp [wearsCap], cynthiaCredence_coe]
    norm_num
  have hinter : cynthiaCredence.real (wearsCap ∩ warriorsCap) = 1 / 3 := by
    rw [show wearsCap ∩ warriorsCap = ↑({.cw} : Finset W) by
      ext w; cases w <;> simp [wearsCap, warriorsCap], cynthiaCredence_coe]
    norm_num
  refine ⟨by rw [hwears]; norm_num, ?_⟩
  rw [measureReal_def, cond_real_apply cynthiaCredence MeasurableSet.of_discrete, ← measureReal_def,
    ← measureReal_def, hwears, hinter]
  norm_num

/-- No proposition over the Sports Fan model has probability 1/2, since every probability is a
multiple of 1/3. -/
theorem no_unconditional_one_half (S : Set W) : cynthiaCredence.real S ≠ 1 / 2 := by
  rw [← (Set.toFinite S).coe_toFinset, cynthiaCredence_coe]
  intro h
  field_simp at h
  have h' : (Set.toFinite S).toFinset.card * 2 = 3 := by exact_mod_cast h
  omega

end CarianiSantorio2018
