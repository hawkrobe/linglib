import Linglib.Semantics.Conditionals.Counterfactual
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# Ciardelli, Zhang and Champollion 2018: Two switches in the theory of counterfactuals

Two switches at the ends of a hallway control a light, on iff they are in the same position;
both are up and the light is on (Fig. 1). Participants judged *if switch A were down, the light
would be off* and its B counterpart true by a majority, and *if switch A or switch B were down*
likewise, but not *if switches A and B were not both up, the light would be off*, though its
antecedent is the De Morgan equivalent of the disjunction (Table 3). The contrast falsifies
every minimal-change semantics, not one choice of similarity: whenever the two simple
counterfactuals are true, any counterfactual quantifying over the closest antecedent worlds
makes the not-both-up one true as well, a closest not-both-up world in which A is down being a
closest A-down world (§1.2), and the argument extends to [kratzer-1981]'s premise semantics
(§6.3). The paper's positive proposal, a background semantics with the inquisitive lifting of
disjunction (§3.2, §4), is not represented.

The four worlds, the wiring law and the five clauses are `World`, `lightOn` and the
propositions `aDn` to `lightOff`, with `aOrBdn_eq_notBothUp` the De Morgan identity; under the
Hamming similarity `hammingSim` the conditional of the closest worlds, `Conditional.closestImp`,
makes all four counterfactuals true at the actual world, and `selectionalCounterfactual` and
`homogeneityCounterfactual` make the falsified one true as well. `minimal_change_forces_notBothUp`
is the §1.2 argument for any similarity ordering and consequent: a closest world of a union is a
closest world of one of its parts (`SimilarityOrdering.closest_union_subset`); the three
operators' versions are corollaries.
The Table 3 counts are the rationals `trueRate_*`, `table3_pattern` the majority pattern the
paper reads off them and `deMorgan_antecedents_diverge` the divergence of the equivalent pair.

## References

* [I. Ciardelli, L. Zhang and L. Champollion, *Two switches in the theory of counterfactuals: A
  study of truth conditionality and minimal change* (2018)][ciardelli-zhang-champollion-2018]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
-/

namespace CiardelliZhangChampollion2018

open Conditional (SimilarityOrdering closestImp mem_closestImp_union)
open Conditional.Counterfactual
  (selectionalCounterfactual selectionalCounterfactual_eq_true_iff homogeneityCounterfactual
   PresupStatus PresupResult)

/-! ### The switches scenario (Fig. 1) -/

/-- The four worlds, by the positions of A and B: `u` up, `d` down. -/
inductive World where
  | uu | ud | du | dd
  deriving Repr, DecidableEq, Fintype

/-- Switch A is up. -/
abbrev aUp : Set World := {.uu, .ud}
/-- Switch B is up. -/
abbrev bUp : Set World := {.uu, .du}

/-- The wiring: the light is on iff the switches are in the same position. -/
abbrev lightOn : Set World := {.uu, .dd}

/-- *Switch A is down.* -/
abbrev aDn : Set World := aUpᶜ
/-- *Switch B is down.* -/
abbrev bDn : Set World := bUpᶜ
/-- *Switch A is down or switch B is down.* -/
abbrev aOrBdn : Set World := aDn ∪ bDn
/-- *Switches A and B are not both up.* -/
abbrev notBothUp : Set World := (aUp ∩ bUp)ᶜ
/-- *The light is off.* -/
abbrev lightOff : Set World := lightOnᶜ

/-! ### De Morgan equivalence -/

/-- The two antecedents have the same truth conditions. -/
theorem aOrBdn_eq_notBothUp : aOrBdn = notBothUp := (Set.compl_inter aUp bUp).symm

/-! ### Predictions under Hamming similarity -/

/-- The number of switches on which two worlds differ. -/
def hamming : World → World → Nat
  | .uu, .uu | .ud, .ud | .du, .du | .dd, .dd => 0
  | .uu, .ud | .ud, .uu | .du, .dd | .dd, .du => 1
  | .uu, .du | .du, .uu | .ud, .dd | .dd, .ud => 1
  | .uu, .dd | .dd, .uu => 2
  | .ud, .du | .du, .ud => 2

/-- Similarity by Hamming distance, one natural ordering on the scenario. -/
def hammingSim : SimilarityOrdering World where
  closer w₀ w₁ w₂ := hamming w₀ w₁ ≤ hamming w₀ w₂
  closer_refl _ _ := Nat.le_refl _
  closer_trans _ _ _ _ h₁ h₂ := h₁.trans h₂
  decClose _ _ _ := Nat.decLe _ _

/-- *If A were down, the light would be off* is true at the actual world: the closest A-down
world is `du`. -/
theorem aDn_off_at_uu :
    .uu ∈ closestImp hammingSim aDn lightOff := by decide

/-- *If B were down, the light would be off* is true at the actual world. -/
theorem bDn_off_at_uu :
    .uu ∈ closestImp hammingSim bDn lightOff := by decide

/-- *If A or B were down, the light would be off* is true at the actual world: the closest
worlds are `ud` and `du`. -/
theorem aOrBdn_off_at_uu :
    .uu ∈ closestImp hammingSim aOrBdn lightOff := by decide

/-- *If A and B were not both up, the light would be off* is predicted true at the actual world,
the antecedent being equivalent to the disjunction; participants judged it true only by a
minority (Table 3). -/
theorem notBothUp_off_at_uu :
    .uu ∈ closestImp hammingSim notBothUp lightOff := by decide

/-- The selectional counterfactual makes the same prediction. -/
theorem selectional_notBothUp_off_at_uu :
    selectionalCounterfactual hammingSim notBothUp lightOff .uu = .true := by
  decide

/-- The homogeneity counterfactual makes the same prediction, with its presupposition satisfied.
-/
theorem homogeneity_notBothUp_off_at_uu :
    homogeneityCounterfactual hammingSim notBothUp lightOff .uu =
      { presupposition := .satisfied, assertion := some true } := by
  decide

/-! ### Minimal change forces the equivalence (§1.2) -/

/-- For any similarity ordering and consequent, if the A-down and the B-down counterfactuals
are true, so is the not-both-up one: a closest not-both-up world is a closest A-down or a closest
B-down world. -/
theorem minimal_change_forces_notBothUp (sim : SimilarityOrdering World) (w₀ : World)
    {C : Set World} (h_a : w₀ ∈ closestImp sim aDn C) (h_b : w₀ ∈ closestImp sim bDn C) :
    w₀ ∈ closestImp sim notBothUp C :=
  aOrBdn_eq_notBothUp ▸ mem_closestImp_union h_a h_b

private theorem homogeneity_eq_true_iff (sim : SimilarityOrdering World) (A C : Set World)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ C)] (w : World) :
    homogeneityCounterfactual sim A C w =
        { presupposition := .satisfied, assertion := some true } ↔ w ∈ closestImp sim A C := by
  unfold homogeneityCounterfactual
  split_ifs <;> simp_all

/-- The selectional counterfactual's true verdict is the same quantifier. -/
theorem selectional_minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : selectionalCounterfactual sim aDn lightOff w₀ = .true)
    (h_b : selectionalCounterfactual sim bDn lightOff w₀ = .true) :
    selectionalCounterfactual sim notBothUp lightOff w₀ = .true := by
  rw [selectionalCounterfactual_eq_true_iff] at *
  exact minimal_change_forces_notBothUp sim w₀ h_a h_b

/-- The homogeneity counterfactual's true verdict, with its presupposition satisfied, is the
same quantifier. -/
theorem homogeneity_minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : homogeneityCounterfactual sim aDn lightOff w₀ =
      { presupposition := .satisfied, assertion := some true })
    (h_b : homogeneityCounterfactual sim bDn lightOff w₀ =
      { presupposition := .satisfied, assertion := some true }) :
    homogeneityCounterfactual sim notBothUp lightOff w₀ =
      { presupposition := .satisfied, assertion := some true } := by
  rw [homogeneity_eq_true_iff] at *
  exact minimal_change_forces_notBothUp sim w₀ h_a h_b

/-! ### The main experiment (Table 3) -/

/-- The proportion judged true of *if A were down, the light would be off*. -/
def trueRate_aDn_off : ℚ := 169 / 256
/-- The proportion judged true of *if B were down, the light would be off*. -/
def trueRate_bDn_off : ℚ := 153 / 235
/-- The proportion judged true of *if A or B were down, the light would be off*. -/
def trueRate_aOrBdn_off : ℚ := 251 / 362
/-- The proportion judged true of *if A and B were not both up, the light would be off*. -/
def trueRate_notBothUp_off : ℚ := 82 / 372
/-- The proportion judged true of *if A and B were not both up, the light would be on*. -/
def trueRate_notBothUp_on : ℚ := 43 / 200

/-- The first three sentences were judged true by a majority and the two not-both-up sentences
were not. -/
theorem table3_pattern :
    (1 / 2 < trueRate_aDn_off ∧ 1 / 2 < trueRate_bDn_off ∧
      1 / 2 < trueRate_aOrBdn_off) ∧
    trueRate_notBothUp_off < 1 / 2 ∧ trueRate_notBothUp_on < 1 / 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    norm_num [trueRate_aDn_off, trueRate_bDn_off, trueRate_aOrBdn_off,
      trueRate_notBothUp_off, trueRate_notBothUp_on]

/-- The De Morgan pair diverges: the disjunctive antecedent was judged true more often than its
equivalent. -/
theorem deMorgan_antecedents_diverge :
    trueRate_notBothUp_off < trueRate_aOrBdn_off := by
  norm_num [trueRate_aOrBdn_off, trueRate_notBothUp_off]

end CiardelliZhangChampollion2018
