/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Modality.Selectional
import Linglib.Semantics.Conditionals.WillConditional
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Core.Probability.Finite
import Mathlib.Tactic.DeriveFintype

/-!
# Cariani and Santorio 2018: will done better

This file formalizes the selectional analysis of the future modal in [cariani-santorio-2018].
*Will* is a modal — it embeds, scopes and interacts with negation — but not a quantifier over
worlds: `will A` is true at `w` when `A` holds at the single world a [stalnaker-1968] selection
function picks out of the historical alternatives. Quantificational accounts fail two further
desiderata that this one meets by construction. *Will* is scopeless, `¬ will A` and `will ¬A`
being equivalent, which universal quantification over a non-trivial modal base cannot deliver;
and sincere assertion of `will A` requires only non-extreme credence, whereas a universal reading
makes any open future-claim false and so demands credence 0.

The Sports Fan scenario is the worked model: Cynthia wears a Warriors cap, a Giants cap, or no
cap tomorrow according to a fair three-way process, and an agent gives each option credence 1/3.
The selectional content of *Cynthia will wear a Warriors cap* is just the Warriors-cap worlds, so
it inherits credence 1/3, while the universal reading is false throughout and gets credence 0.
The same model shows the account's limit: no proposition over it has probability 1/2, so the
selectional content of *if Cynthia wears a cap, she will wear a Warriors cap* cannot take the
value the corresponding conditional probability does — an instance of [hajek-1989]'s observation
that conditional probability values outnumber unconditional ones.

## Main definitions

* `W`, `histAlt`, `cynthiaSel`, `cynthiaPMF` — the Sports Fan worlds, alternatives, selection
  function and credences

## Main results

* `cynthia_credence_one_third`, `universal_will_credence_zero` — the cognitive-role contrast
* `cap_will_conditional_cem`, `universal_will_conditional_cem_fails` — will-conditionals validate
  Compositional CEM on the selectional reading and refute it on the universal one
* `no_unconditional_one_half`, `cap_warriors_credence_one_half` — no proposition over the model
  has the probability the conditional does

## References

* [cariani-santorio-2018]
* [stalnaker-1968]
* [hajek-1989]
-/

namespace CarianiSantorio2018

open _root_.Conditionals (SelectionFunction)
open Modality.Selectional
open Conditionals.WillConditional (willConditional universalWillConditional compositional_CEM)
open scoped ENNReal

/-! ### The Sports Fan model -/

/-- The three worlds of the Sports Fan scenario (§2.3), the modal base of *Cynthia will wear a
Warriors cap*: she wears a Warriors cap, a Giants cap, or no cap. -/
inductive W where
  | cw | cg | cn
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The modal parameter: every cap-choice is historically open, nothing being settled at the time
of utterance. -/
def histAlt : Set W := { .cw, .cg, .cn }

/-- Proposition: "Cynthia wears a Warriors cap." -/
def warriorsCap : Set W := {.cw}

instance : DecidablePred (· ∈ warriorsCap) := fun w => decEq w .cw

/-- Proposition: "Cynthia wears *some* cap" (Warriors or Giants). -/
def wearsCap : Set W := {.cw, .cg}

instance : DecidablePred (· ∈ wearsCap) := fun w =>
  inferInstanceAs (Decidable (w = .cw ∨ w ∈ ({.cg} : Set W)))

/-- The underlying selection function: prefer `w` if `w ∈ A`,
    otherwise the first available element in the order cw, cg, cn.
    This is total because `W` is exhausted by `{cw, cg, cn}`. -/
noncomputable def selFn (w : W) (A : Set W) : W :=
  open Classical in
  if w ∈ A then w else
  if (W.cw : W) ∈ A then .cw else
  if (W.cg : W) ∈ A then .cg else .cn

/-- `selFn` satisfies [stalnaker-1968]'s Inclusion axiom. -/
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

/-- `selFn` satisfies [stalnaker-1968]'s Centering axiom. -/
theorem selFn_centering (w : W) (A : Set W) (hw : w ∈ A) :
    selFn w A = w := by
  unfold selFn
  rw [if_pos hw]

noncomputable def cynthiaSel : SelectionFunction W where
  sel := selFn
  inclusion := selFn_inclusion
  centering := selFn_centering

/-- The preference `selFn` induces on the three worlds is transitive. [cariani-santorio-2018]
impose only Inclusion and Centering, leaving [stalnaker-1968]'s further constraints open (§5.2
fn. 17); this witness satisfies them anyway, ordering the worlds `cw < cg < cn` from any centre
not itself among the candidates. -/
theorem cynthiaSel_coherent : cynthiaSel.isCoherent := by
  intro w₀ w₁ w₂ w₃ h12 h23
  unfold _root_.Conditionals.selectionPrefers cynthiaSel selFn at *
  revert h12 h23
  cases w₀ <;> cases w₁ <;> cases w₂ <;> cases w₃ <;>
    simp_all (config := { decide := true })

/-! ### Modal subordination -/

/-- At the Warriors-cap world, *Cynthia will wear a Warriors cap* is true: Centering makes the
selected world the world of evaluation, so the claim reduces to its prejacent. -/
theorem cynthia_will_warriors_cap :
    willSem cynthiaSel warriorsCap histAlt .cw := by
  rw [unembedded_collapse cynthiaSel warriorsCap histAlt .cw
      (by simp [histAlt])]
  trivial



/-- A modal parameter that *excludes* the actual world `cw` (here taken
    as the world from which Cynthia evaluates): the speaker is reasoning
    about a counterfactual continuation in which Cynthia wears no cap. -/
def counterfactualAlt : Set W := { .cn }

/-- Where the world of evaluation is outside the modal parameter the collapse fails: the
selection function must leave it, and the claim can diverge from its prejacent. -/
theorem nonmember_no_collapse :
    ¬ willSem cynthiaSel warriorsCap counterfactualAlt .cw := by
  show selFn .cw counterfactualAlt ∉ warriorsCap
  unfold selFn counterfactualAlt
  simp [warriorsCap]

/-- Where the world of evaluation is in the modal parameter, Centering collapses `will A` to its
prejacent — which is what makes an unembedded will-claim inherit its prejacent's credence. -/
theorem member_collapses (A : W → Prop) (w : W) (hw : w ∈ histAlt) :
    willSem cynthiaSel A histAlt w ↔ A w :=
  unembedded_collapse cynthiaSel A histAlt w hw

/-! ### The cognitive role of a will-claim -/

/-- The universe of `W` enumerated as a 3-element `Finset` —
    used to reduce `∑ w : W, f w` to `f cw + f cg + f cn`. -/
private lemma univ_W_eq : (Finset.univ : Finset W) = {.cw, .cg, .cn} := by
  ext w; cases w <;> decide

/-- The agent's credences over the historical alternatives: uniform, each cap choice getting
1/3. -/
noncomputable def cynthiaPMF : PMF W :=
  PMF.ofFintype (fun _ => (1 : ℝ≥0∞) / 3) (by
    rw [univ_W_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    ennreal_arith)

/-- `cynthiaPMF` is supported on `histAlt`: the support lies inside the
    modal parameter. Vacuously true here, since every world is in
    `histAlt` — but the discipline matches the `cognitive_role`
    interface, which takes `μ.support ⊆ f`. -/
theorem cynthiaPMF_support_in_histAlt : cynthiaPMF.support ⊆ histAlt := by
  intro w _
  cases w <;> simp [histAlt]

/-- Transparency (§8.1): the credence in *Cynthia will wear a Warriors cap* is the credence in
its prejacent, so a will-claim about an open future carries non-extreme credence. -/
theorem cynthia_credence_one_third :
    cynthiaPMF.probOfSet {w | cynthiaSel.sel w histAlt ∈ warriorsCap} = 1/3 := by
  rw [cognitive_role cynthiaSel warriorsCap histAlt cynthiaPMF
      cynthiaPMF_support_in_histAlt]
  rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      if_pos (show (W.cw) ∈ warriorsCap by decide),
      if_neg (show (W.cg) ∉ warriorsCap by decide),
      if_neg (show (W.cn) ∉ warriorsCap by decide)]
  simp only [cynthiaPMF, PMF.ofFintype_apply]
  ennreal_arith

/-- The universal-quantifier reading of *will Warriors-cap* is false at
    every world: `histAlt` contains the Giants-cap world `cg` where
    `warriorsCap` is False, so the universal cannot hold. -/
theorem universalWill_warriorsCap_const_false (w : W) :
    ¬ universalWill warriorsCap histAlt w := by
  intro h
  have hcg : W.cg ∈ warriorsCap := h .cg (by simp [histAlt])
  simp [warriorsCap] at hcg

/-- The universal reading gets credence 0, since the universal is false wherever the future is
open. This is the cognitive-role argument: a rational agent's non-extreme credence in a
will-claim is unavailable on a quantificational semantics. -/
theorem universal_will_credence_zero :
    cynthiaPMF.probOfSet {w | universalWill warriorsCap histAlt w} = 0 := by
  have hempty : {w | universalWill warriorsCap histAlt w} = (∅ : Set W) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact universalWill_warriorsCap_const_false w
  rw [hempty, PMF.probOfSet_empty]

/-! ### The cap-conditional -/

/-- The value a degree of belief in *if Cynthia wears a cap, she will wear a Warriors cap*
naturally takes: of the cap-wearing worlds, which carry mass 2/3, the Warriors-cap world carries
1/3. No proposition over this model has that probability (`no_unconditional_one_half`), so the
selectional content of the conditional cannot take it — it is 1/3 or 2/3 depending on which world
the selection function returns at the no-cap world. [cariani-santorio-2018] recover the value by
refining the algebra to world-and-selection-function pairs. -/
theorem cap_warriors_credence_one_half :
    cynthiaPMF.probOfSet wearsCap ≠ 0 ∧
    cynthiaPMF.condProbSet wearsCap warriorsCap = 1/2 := by
  -- Compute `probOfSet wearsCap = 2/3` once, reuse for both conjuncts.
  have hwears : cynthiaPMF.probOfSet wearsCap = 2/3 := by
    rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        if_pos (show (W.cw) ∈ wearsCap by decide),
        if_pos (show (W.cg) ∈ wearsCap by decide),
        if_neg (show (W.cn) ∉ wearsCap by decide)]
    simp only [cynthiaPMF, PMF.ofFintype_apply]
    ennreal_arith
  have hinter : cynthiaPMF.probOfSet (wearsCap ∩ warriorsCap) = 1/3 := by
    rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        if_pos (show (W.cw) ∈ wearsCap ∩ warriorsCap by decide),
        if_neg (show (W.cg) ∉ wearsCap ∩ warriorsCap by decide),
        if_neg (show (W.cn) ∉ wearsCap ∩ warriorsCap by decide)]
    simp only [cynthiaPMF, PMF.ofFintype_apply]
    ennreal_arith
  refine ⟨?_, ?_⟩
  · rw [hwears, ← pos_iff_ne_zero]; ennreal_arith
  · rw [PMF.condProbSet_eq_div, hwears, hinter]
    -- (1/3) / (2/3) = 1/2 in ENNReal — `ennreal_arith` lifts to ℝ
    ennreal_arith

/-! ### Conditional excluded middle

Compositional CEM — `(if A, will B) ∨ (if A, will ¬B)` — follows from the single-valuedness of
selection (§7). The universal-base reading refutes it on the same restricted parameter
`histAlt ∩ ‖cap‖ = {cw, cg}`, which holds both a Warriors-cap world and a Giants-cap one. -/

/-- **Selectional will-conditionals validate Compositional CEM**
    (paper §7): for the cap-conditional on the Sports Fan model,
    `(if cap, will Warriors) ∨ (if cap, will ¬Warriors)` holds. Inherited
    from the generic `WillConditional.compositional_CEM`. -/
theorem cap_will_conditional_cem :
    willConditional cynthiaSel wearsCap warriorsCap histAlt .cw ∨
    willConditional cynthiaSel wearsCap (fun w => ¬ warriorsCap w) histAlt .cw :=
  compositional_CEM cynthiaSel wearsCap warriorsCap histAlt .cw

/-- **The universal-base reading refutes Compositional CEM** — the
    will-conditional analogue of `Stalnaker1981.bizet_cem_fails_universal`.
    On the restricted parameter `histAlt ∩ ‖cap‖ = {cw, cg}`, neither
    `(if cap, will Warriors)` nor `(if cap, will ¬Warriors)` is
    universally true: `cg` is a cap-world that is not a Warriors-world
    (killing the first disjunct) and `cw` is a Warriors-world (killing the
    second). So the Lewis-style universal future-conditional falsifies the
    CEM that the selectional analysis validates. -/
theorem universal_will_conditional_cem_fails :
    ¬ universalWillConditional wearsCap warriorsCap histAlt .cw ∧
    ¬ universalWillConditional wearsCap (fun w => ¬ warriorsCap w) histAlt .cw := by
  unfold universalWillConditional _root_.Modality.Selectional.universalWill
    _root_.Conditionals.WillConditional.restrict
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hcg : (W.cg) ∈ warriorsCap :=
      h .cg ⟨by simp [histAlt], show (W.cg) ∈ wearsCap by decide⟩
    exact absurd hcg (by decide)
  · have hcw : ¬ (W.cw) ∈ warriorsCap :=
      h .cw ⟨by simp [histAlt], show (W.cw) ∈ wearsCap by decide⟩
    exact absurd (show (W.cw) ∈ warriorsCap by decide) hcw

/-! ### The limit of the account -/

/-- No proposition over the Sports Fan model has probability 1/2: with three worlds at 1/3 each,
every probability lands in `{0, 1/3, 2/3, 1}`. This is [hajek-1989]'s point in miniature —
conditional probability values outnumber unconditional ones, so some conditional probability has
no proposition to match it, and a semantics that gives a conditional a proposition as its content
cannot always give it the value it intuitively takes. -/
theorem no_unconditional_one_half (S : Set W) [DecidablePred (· ∈ S)] :
    cynthiaPMF.probOfSet S ≠ 1/2 := by
  rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [cynthiaPMF, PMF.ofFintype_apply]
  intro heq
  have h := congrArg ENNReal.toReal heq
  -- 8 cases: each of cw, cg, cn either in S or not
  by_cases hcw : (W.cw) ∈ S <;>
    by_cases hcg : (W.cg) ∈ S <;>
    by_cases hcn : (W.cn) ∈ S <;>
    (simp [hcw, hcg, hcn, ENNReal.toReal_add,
           ENNReal.toReal_ofNat, ENNReal.add_eq_top] at h
     try norm_num at h)

end CarianiSantorio2018
