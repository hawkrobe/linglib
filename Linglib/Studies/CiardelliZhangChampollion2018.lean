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

The four worlds, the wiring law and the five clauses are `World`, `lightOn` and the predicates
`aDn` to `lightOff`, with `aOrBdn_eq_notBothUp` the De Morgan identity; under the Hamming
similarity `hammingSim` the substrate's `universalCounterfactual` makes all four counterfactuals
true at the actual world, and `selectionalCounterfactual` and `homogeneityCounterfactual` make
the falsified one true as well. `closestWorlds_predicate_forces_notBothUp` is the §1.2 argument
for any similarity ordering and consequent, with the three operators' versions as corollaries.
The Table 3 counts are the rationals `trueRate_*`, `table3_pattern` the majority pattern the
paper reads off them and `deMorgan_antecedents_diverge` the divergence of the equivalent pair.

## References

* [I. Ciardelli, L. Zhang and L. Champollion, *Two switches in the theory of counterfactuals: A
  study of truth conditionality and minimal change* (2018)][ciardelli-zhang-champollion-2018]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
-/

namespace CiardelliZhangChampollion2018

open Conditionals (SimilarityOrdering)
open Conditionals.Counterfactual
  (universalCounterfactual selectionalCounterfactual homogeneityCounterfactual
   PresupStatus PresupResult)

/-! ### The switches scenario (Fig. 1) -/

/-- The four worlds, by the positions of A and B: `u` up, `d` down. -/
inductive World where
  | uu | ud | du | dd
  deriving Repr, DecidableEq, Fintype

/-- Switch A is up. -/
def aUp : World → Prop | .uu | .ud => True | .du | .dd => False
/-- Switch B is up. -/
def bUp : World → Prop | .uu | .du => True | .ud | .dd => False

/-- The wiring: the light is on iff the switches are in the same position. -/
def lightOn : World → Prop | .uu | .dd => True | .ud | .du => False

/-- *Switch A is down.* -/
def aDn (w : World) : Prop := ¬ aUp w
/-- *Switch B is down.* -/
def bDn (w : World) : Prop := ¬ bUp w
/-- *Switch A is down or switch B is down.* -/
def aOrBdn (w : World) : Prop := aDn w ∨ bDn w
/-- *Switches A and B are not both up.* -/
def notBothUp (w : World) : Prop := ¬ (aUp w ∧ bUp w)
/-- *The light is off.* -/
def lightOff (w : World) : Prop := ¬ lightOn w

instance : DecidablePred aUp := fun w => by cases w <;> simp only [aUp] <;> infer_instance
instance : DecidablePred bUp := fun w => by cases w <;> simp only [bUp] <;> infer_instance
instance : DecidablePred lightOn := fun w => by cases w <;> simp only [lightOn] <;> infer_instance
instance : DecidablePred aDn := fun _ => inferInstanceAs (Decidable (¬ _))
instance : DecidablePred bDn := fun _ => inferInstanceAs (Decidable (¬ _))
instance : DecidablePred aOrBdn := fun _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred notBothUp := fun _ => inferInstanceAs (Decidable (¬ _))
instance : DecidablePred lightOff := fun _ => inferInstanceAs (Decidable (¬ _))

/-! ### De Morgan equivalence -/

theorem aOrBdn_iff_notBothUp (w : World) : aOrBdn w ↔ notBothUp w := by
  cases w <;> decide

/-- The two antecedents have the same truth conditions. -/
theorem aOrBdn_eq_notBothUp : aOrBdn = notBothUp := by
  funext w
  exact propext (aOrBdn_iff_notBothUp w)

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
    universalCounterfactual hammingSim aDn lightOff .uu := by decide

/-- *If B were down, the light would be off* is true at the actual world. -/
theorem bDn_off_at_uu :
    universalCounterfactual hammingSim bDn lightOff .uu := by decide

/-- *If A or B were down, the light would be off* is true at the actual world: the closest
worlds are `ud` and `du`. -/
theorem aOrBdn_off_at_uu :
    universalCounterfactual hammingSim aOrBdn lightOff .uu := by decide

/-- *If A and B were not both up, the light would be off* is predicted true at the actual world,
the antecedent being equivalent to the disjunction; participants judged it true only by a
minority (Table 3). -/
theorem notBothUp_off_at_uu :
    universalCounterfactual hammingSim notBothUp lightOff .uu := by decide

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

/-- For any similarity ordering and consequent `B`, if every closest A-down world and every
closest B-down world is `B`, so is every closest not-both-up world: such a world is A-down or
B-down, and then a closest world of that antecedent
(`SimilarityOrdering.mem_closestWorlds_of_subset`). -/
theorem closestWorlds_predicate_forces_notBothUp
    (sim : SimilarityOrdering World) (w₀ : World)
    (B : World → Prop) [DecidablePred B]
    (h_a : ∀ w' ∈ sim.closestWorlds w₀ (Finset.univ.filter aDn), B w')
    (h_b : ∀ w' ∈ sim.closestWorlds w₀ (Finset.univ.filter bDn), B w') :
    ∀ w' ∈ sim.closestWorlds w₀ (Finset.univ.filter notBothUp), B w' := by
  intro w hw
  have hwNAB : notBothUp w := (Finset.mem_filter.mp
    ((SimilarityOrdering.mem_closestWorlds _ _ _ _).mp hw).1).2
  have h_aDn_sub : Finset.univ.filter aDn ⊆ Finset.univ.filter notBothUp := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun ⟨hA, _⟩ => hx.2 hA⟩
  have h_bDn_sub : Finset.univ.filter bDn ⊆ Finset.univ.filter notBothUp := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun ⟨_, hB⟩ => hx.2 hB⟩
  by_cases hwA : aDn w
  · exact h_a w (sim.mem_closestWorlds_of_subset h_aDn_sub hw
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwA⟩))
  · have hwB : bDn w := fun hbU =>
      hwNAB ⟨by by_contra hnA; exact hwA hnA, hbU⟩
    exact h_b w (sim.mem_closestWorlds_of_subset h_bDn_sub hw
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwB⟩))

/-- The universal counterfactual is the quantifier over closest worlds. -/
theorem minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : universalCounterfactual sim aDn lightOff w₀)
    (h_b : universalCounterfactual sim bDn lightOff w₀) :
    universalCounterfactual sim notBothUp lightOff w₀ :=
  closestWorlds_predicate_forces_notBothUp sim w₀ lightOff h_a h_b

private theorem selectional_eq_true_iff
    (sim : SimilarityOrdering World) (A B : World → Prop)
    [DecidablePred A] [DecidablePred B] (w : World) :
    selectionalCounterfactual sim A B w = .true ↔
      ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w' := by
  unfold selectionalCounterfactual
  constructor
  · intro heq
    by_contra h_neg
    rw [if_neg h_neg] at heq
    split_ifs at heq
  · intro h
    rw [if_pos h]

private theorem homogeneity_eq_true_iff
    (sim : SimilarityOrdering World) (A B : World → Prop)
    [DecidablePred A] [DecidablePred B] (w : World) :
    homogeneityCounterfactual sim A B w =
        { presupposition := .satisfied, assertion := some true } ↔
      ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w' := by
  unfold homogeneityCounterfactual
  constructor
  · intro heq
    by_contra h_neg
    rw [if_neg h_neg] at heq
    split_ifs at heq <;> injection heq with h1 h2 <;> cases h2
  · intro h
    rw [if_pos h]

/-- The selectional counterfactual's true verdict is the same quantifier. -/
theorem selectional_minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : selectionalCounterfactual sim aDn lightOff w₀ = .true)
    (h_b : selectionalCounterfactual sim bDn lightOff w₀ = .true) :
    selectionalCounterfactual sim notBothUp lightOff w₀ = .true :=
  (selectional_eq_true_iff sim notBothUp lightOff w₀).mpr
    (closestWorlds_predicate_forces_notBothUp sim w₀ lightOff
      ((selectional_eq_true_iff sim aDn lightOff w₀).mp h_a)
      ((selectional_eq_true_iff sim bDn lightOff w₀).mp h_b))

/-- The homogeneity counterfactual's true verdict, with its presupposition satisfied, is the
same quantifier. -/
theorem homogeneity_minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : homogeneityCounterfactual sim aDn lightOff w₀ =
      { presupposition := .satisfied, assertion := some true })
    (h_b : homogeneityCounterfactual sim bDn lightOff w₀ =
      { presupposition := .satisfied, assertion := some true }) :
    homogeneityCounterfactual sim notBothUp lightOff w₀ =
      { presupposition := .satisfied, assertion := some true } :=
  (homogeneity_eq_true_iff sim notBothUp lightOff w₀).mpr
    (closestWorlds_predicate_forces_notBothUp sim w₀ lightOff
      ((homogeneity_eq_true_iff sim aDn lightOff w₀).mp h_a)
      ((homogeneity_eq_true_iff sim bDn lightOff w₀).mp h_b))

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
