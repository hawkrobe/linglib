/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Modality.Selectional
public import Linglib.Semantics.Conditionals.WillConditional
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Core.Probability.UniformOn
public import Linglib.Core.Probability.ConditionalProbability
public import Mathlib.Tactic.DeriveFintype

/-!
# Cariani and Santorio 2018: will done better

This file formalizes the selectional analysis of the future modal by Cariani and Santorio. *Will*
is a modal — it embeds, scopes and interacts with negation — but not a quantifier over worlds:
`will A` is true at `w` when `A` holds at the single world that a Stalnaker selection function
picks out of the historical alternatives. Quantificational accounts fail two further desiderata
that this one meets by construction. *Will* is scopeless, `¬ will A` and `will ¬A` being
equivalent, which universal quantification over a non-trivial modal base cannot deliver; and
sincere assertion of `will A` requires only non-extreme credence, whereas a universal reading
makes any open future-claim false and so demands credence 0.

The Sports Fan scenario is the worked model: Cynthia wears a Warriors cap, a Giants cap, or no cap
tomorrow according to a fair three-way process, and an agent gives each option credence 1/3. The
selectional content of *Cynthia will wear a Warriors cap* is just the Warriors-cap worlds, so it
inherits credence 1/3, while the universal reading is false throughout and gets credence 0. The
same model shows the account's limit: no proposition over it has probability 1/2, so the
selectional content of *if Cynthia wears a cap, she will wear a Warriors cap* cannot take the
value the corresponding conditional probability does — an instance of Hájek's observation that
conditional probability values outnumber unconditional ones.

## Main definitions

* `W`, `histAlt`, `cynthiaSel`, `cynthiaCredence` — the Sports Fan worlds, alternatives, selection
  function and credences

## Main results

* `cynthia_credence_one_third`, `universal_will_credence_zero` — the cognitive-role contrast
* `cap_will_conditional_cem`, `universal_will_conditional_cem_fails` — will-conditionals validate
  Compositional CEM on the selectional reading and refute it on the universal one
* `no_unconditional_one_half`, `cap_warriors_credence_one_half` — no proposition over the model
  has the probability the conditional does

## References

* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [A. Hajek, *Probabilities of Conditionals — Revisited* (1989)][hajek-1989]
-/

@[expose] public section

namespace CarianiSantorio2018

open _root_.Conditional (SelectionFunction)
open Modality.Selectional
open Conditional.WillConditional (willConditional universalWillConditional compositional_CEM)
open MeasureTheory ProbabilityTheory

/-! ### The Sports Fan model -/

/-- The three worlds of the Sports Fan scenario (§2.3) form the modal base of *Cynthia will wear a
Warriors cap*. She wears a Warriors cap, a Giants cap, or no cap. -/
inductive W where
  | cw | cg | cn
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- In the modal parameter every cap choice is historically open, nothing being settled at the time
of utterance. -/
def histAlt : Set W := { .cw, .cg, .cn }

/-- The proposition that Cynthia wears a Warriors cap. -/
def warriorsCap : Set W := {.cw}

instance : DecidablePred (· ∈ warriorsCap) := fun w ↦ decEq w .cw

/-- The proposition that Cynthia wears some cap, Warriors or Giants. -/
def wearsCap : Set W := {.cw, .cg}

instance : DecidablePred (· ∈ wearsCap) := fun w ↦
  inferInstanceAs (Decidable (w = .cw ∨ w ∈ ({.cg} : Set W)))

/-- The underlying selection function prefers `w` if `w ∈ A`, and otherwise the first available
element in the order cw, cg, cn. It is total because `W` is exhausted by `{cw, cg, cn}`. -/
noncomputable def selFn (w : W) (A : Set W) : W :=
  open Classical in
  if w ∈ A then w else
  if (W.cw : W) ∈ A then .cw else
  if (W.cg : W) ∈ A then .cg else .cn

/-- `selFn` satisfies Stalnaker's Inclusion axiom. -/
theorem selFn_inclusion (w : W) (A : Set W) (hA : A.Nonempty) :
    selFn w A ∈ A := by
  unfold selFn
  split_ifs with hw h0 h1
  · exact hw
  · exact h0
  · exact h1
  · obtain ⟨x, hx⟩ := hA
    cases x
    · exact absurd hx h0
    · exact absurd hx h1
    · exact hx

/-- `selFn` satisfies Stalnaker's Centering axiom. -/
theorem selFn_centering (w : W) (A : Set W) (hw : w ∈ A) :
    selFn w A = w := by
  unfold selFn
  rw [ite_eq_left hw]

noncomputable def cynthiaSel : SelectionFunction W where
  sel := selFn
  inclusion := selFn_inclusion
  centering := selFn_centering

/-- The preference that `selFn` induces on the three worlds is transitive. The paper imposes only
Inclusion and Centering and leaves Stalnaker's further constraints open (§5.2 fn. 17). This witness
satisfies them anyway, ordering the worlds `cw < cg < cn` from any centre not itself among the
candidates. -/
theorem cynthiaSel_coherent : cynthiaSel.isCoherent := by
  intro w₀ w₁ w₂ w₃ h12 h23
  unfold _root_.Conditional.selectionPrefers cynthiaSel selFn at *
  revert h12 h23
  cases w₀ <;> cases w₁ <;> cases w₂ <;> cases w₃ <;>
    simp_all (config := { decide := true })

/-! ### Modal subordination -/

/-- At the Warriors-cap world *Cynthia will wear a Warriors cap* is true, since Centering makes the
selected world the world of evaluation, so the claim reduces to its prejacent. -/
theorem cynthia_will_warriors_cap :
    willSem cynthiaSel warriorsCap histAlt .cw := by
  rw [unembedded_collapse cynthiaSel warriorsCap histAlt .cw
      (by simp [histAlt])]
  trivial



/-- A modal parameter that excludes the actual world `cw`, here taken as the world from which
Cynthia evaluates. The speaker is reasoning about a counterfactual continuation in which Cynthia
wears no cap. -/
def counterfactualAlt : Set W := { .cn }

/-- Where the world of evaluation is outside the modal parameter the collapse fails, since the
selection function must leave it, and the claim can diverge from its prejacent. -/
theorem nonmember_no_collapse :
    ¬ willSem cynthiaSel warriorsCap counterfactualAlt .cw := by
  show selFn .cw counterfactualAlt ∉ warriorsCap
  unfold selFn counterfactualAlt
  simp [warriorsCap]

/-- Where the world of evaluation is in the modal parameter, Centering collapses `will A` to its
prejacent, which is what makes an unembedded will-claim inherit the credence of its prejacent. -/
theorem member_collapses (A : W → Prop) (w : W) (hw : w ∈ histAlt) :
    willSem cynthiaSel A histAlt w ↔ A w :=
  unembedded_collapse cynthiaSel A histAlt w hw

/-! ### The cognitive role of a will-claim -/

instance : MeasurableSpace W := ⊤

instance : MeasurableSingletonClass W := ⟨fun _ ↦ trivial⟩

/-- The agent's credences over the historical alternatives are uniform, each cap choice getting
1/3. -/
noncomputable def cynthiaCredence : Measure W := uniformOn Set.univ

/-- The credences are concentrated on the modal parameter, as `cognitive_role` requires. Here
every world is a historical alternative. -/
theorem cynthiaCredence_histAlt_compl : cynthiaCredence histAltᶜ = 0 := by
  have : histAltᶜ = (∅ : Set W) := by ext w; cases w <;> simp [histAlt]
  rw [this, measure_empty]

private theorem card_W : Fintype.card W = 3 := rfl

private theorem warriorsCap_eq : warriorsCap = ↑({.cw} : Finset W) := by simp [warriorsCap]

private theorem wearsCap_eq : wearsCap = ↑({.cw, .cg} : Finset W) := by simp [wearsCap]

/-- The credence in *Cynthia will wear a Warriors cap* is the credence in its prejacent, so a
will-claim about an open future carries non-extreme credence (transparency, §8.1). -/
theorem cynthia_credence_one_third :
    cynthiaCredence.real {w | cynthiaSel.sel w histAlt ∈ warriorsCap} = 1 / 3 := by
  rw [measureReal_def, cognitive_role cynthiaSel warriorsCap histAlt cynthiaCredence
    cynthiaCredence_histAlt_compl, ← measureReal_def, cynthiaCredence, warriorsCap_eq,
    uniformOn_univ_real_coe_finset, card_W]
  norm_num

/-- The universal reading of *will Warriors-cap* is false at every world, since `histAlt` contains
the Giants-cap world `cg`, where `warriorsCap` fails. -/
theorem universalWill_warriorsCap_const_false (w : W) :
    ¬ universalWill warriorsCap histAlt w := by
  intro h
  have hcg : W.cg ∈ warriorsCap := h .cg (by simp [histAlt])
  simp [warriorsCap] at hcg

/-- The universal reading gets credence 0, since the universal is false wherever the future is open.
This is the cognitive-role argument, that the non-extreme credence of a rational agent in a
will-claim is unavailable on a quantificational semantics. -/
theorem universal_will_credence_zero :
    cynthiaCredence.real {w | universalWill warriorsCap histAlt w} = 0 := by
  have hempty : {w | universalWill warriorsCap histAlt w} = (∅ : Set W) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact universalWill_warriorsCap_const_false w
  rw [hempty, measureReal_empty]

/-! ### The cap-conditional -/

/-- The value that a degree of belief in *if Cynthia wears a cap, she will wear a Warriors cap*
naturally takes is 1/2, since of the cap-wearing worlds, which carry mass 2/3, the Warriors-cap
world carries 1/3. No proposition over this model has that probability
(`no_unconditional_one_half`), so the selectional content of the conditional cannot take it, and is
1/3 or 2/3 depending on which world the selection function returns at the no-cap world. The paper
recovers the value by refining the algebra to pairs of a world and a selection function. -/
theorem cap_warriors_credence_one_half :
    cynthiaCredence.real wearsCap ≠ 0 ∧ cynthiaCredence[|wearsCap].real warriorsCap = 1 / 2 := by
  have hwears : cynthiaCredence.real wearsCap = 2 / 3 := by
    rw [cynthiaCredence, wearsCap_eq, uniformOn_univ_real_coe_finset, card_W]
    norm_num
  have hinter : cynthiaCredence.real (wearsCap ∩ warriorsCap) = 1 / 3 := by
    have : wearsCap ∩ warriorsCap = ↑({.cw} : Finset W) := by
      ext w; cases w <;> simp [wearsCap, warriorsCap]
    rw [cynthiaCredence, this, uniformOn_univ_real_coe_finset, card_W]
    norm_num
  refine ⟨by rw [hwears]; norm_num, ?_⟩
  rw [measureReal_def, cond_real_apply cynthiaCredence MeasurableSet.of_discrete, ← measureReal_def,
    ← measureReal_def, hwears, hinter]
  norm_num

/-! ### Conditional excluded middle

Compositional CEM — `(if A, will B) ∨ (if A, will ¬B)` — follows from the single-valuedness of
selection (§7). The universal-base reading refutes it on the same restricted parameter
`histAlt ∩ ‖cap‖ = {cw, cg}`, which holds both a Warriors-cap world and a Giants-cap one. -/

/-- Selectional will-conditionals validate Compositional CEM (§7). For the cap-conditional on the
Sports Fan model, `(if cap, will Warriors) ∨ (if cap, will ¬Warriors)` holds, by the generic
`WillConditional.compositional_CEM`. -/
theorem cap_will_conditional_cem :
    willConditional cynthiaSel wearsCap warriorsCap histAlt .cw ∨
    willConditional cynthiaSel wearsCap (fun w ↦ ¬ warriorsCap w) histAlt .cw :=
  compositional_CEM cynthiaSel wearsCap warriorsCap histAlt .cw

/-- The universal reading refutes Compositional CEM, the will-conditional analogue of
`Stalnaker1981.bizet_cem_fails_universal`. On the restricted parameter `histAlt ∩ ‖cap‖ = {cw, cg}`,
neither `(if cap, will Warriors)` nor `(if cap, will ¬Warriors)` is universally true, since `cg` is
a cap-world that is not a Warriors-world and `cw` is a Warriors-world. So the universal future
conditional falsifies the CEM that the selectional analysis validates. -/
theorem universal_will_conditional_cem_fails :
    ¬ universalWillConditional wearsCap warriorsCap histAlt .cw ∧
    ¬ universalWillConditional wearsCap (fun w ↦ ¬ warriorsCap w) histAlt .cw := by
  unfold universalWillConditional _root_.Modality.Selectional.universalWill
    _root_.Conditional.WillConditional.restrict
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hcg : (W.cg) ∈ warriorsCap :=
      h .cg ⟨by simp [histAlt], show (W.cg) ∈ wearsCap by decide⟩
    exact absurd hcg (by decide)
  · have hcw : ¬ (W.cw) ∈ warriorsCap :=
      h .cw ⟨by simp [histAlt], show (W.cw) ∈ wearsCap by decide⟩
    exact absurd (show (W.cw) ∈ warriorsCap by decide) hcw

/-! ### The limit of the account -/

/-- No proposition over the Sports Fan model has probability 1/2, since with three worlds at 1/3
each every probability lands in `{0, 1/3, 2/3, 1}`. This is Hájek's point in miniature. Conditional
probability values outnumber unconditional ones, so some conditional probability has no proposition
to match it, and a semantics that gives a conditional a proposition as its content cannot always
give it the value it intuitively takes. -/
theorem no_unconditional_one_half (S : Set W) : cynthiaCredence.real S ≠ 1 / 2 := by
  have hS : S = ↑(Set.toFinite S).toFinset := (Set.Finite.coe_toFinset _).symm
  rw [hS, cynthiaCredence, uniformOn_univ_real_coe_finset, card_W]
  intro h
  field_simp at h
  have h' : (Set.toFinite S).toFinset.card * 2 = 3 := by exact_mod_cast h
  omega

end CarianiSantorio2018
