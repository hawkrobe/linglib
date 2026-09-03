import Linglib.Core.Probability.Confirmation
import Linglib.Semantics.Conditionals.Probabilistic
import Linglib.Data.Examples.ChungMascarenhas2023
import Mathlib.Probability.Distributions.Uniform

/-!
# Chung and Mascarenhas 2023: Modality, expected utility, and hypothesis testing

Necessity modals share one semantics over a family `R` of relevant propositions: `must φ` holds
when the expectation, given `φ`, of the number `μ_R` of propositions in `R` that are true exceeds
a threshold `θ` while no alternative's does (6); read deontically the expectation is `φ`'s
expected utility, read epistemically its explanatory value, the sum of the likelihoods of the
evidence (12), and `ought φ` asks instead that `φ` be strictly best among the good-enough (17).
In [kolodny-macfarlane-2010]'s miners puzzle (§3.1) blocking neither shaft is the only
good-enough option for a threshold between 5 and 9 (26), but once the miners are known to be in
shaft A the conditional *must* needs one between 9 and 10 (25b), an incompatibility the paper
notes; the modal conjunction fallacy ([tversky-kahneman-1983], §3.2) and modal base-rate
neglect ([kahneman-tversky-1973], §3.3) come out true for thresholds between the hypotheses'
explanatory values ((34), (41)); and the Korean conditional evaluative *cip-ey iss-eya toy-n-ta*
composes the evaluative predicate, the conditional, Lassiter's threshold and the *-(e)ya*
exhaustifier into exactly (6) (§4, (48)).

`mustCM`, `oughtCM` and `mustCMWithPlausibility` are (6), (17) and the §5 plausibility patch
over the substrate's `sumLikelihoods`, and `koreanConditionalEvaluative_iff_mustCM` is (48) by
the identity `condExpect_countMeasure`. The miners puzzle is built from Table 1 with the ideals
(18) of [cariani-kaufmann-kaufmann-2013] as an indexed family, and its expected utilities,
*ought* and *must* claims and threshold incompatibility are derived from the uniform prior;
modal Linda and modal Lawyers keep the paper's stipulated conditional probabilities as
rationals, the text fixing no joint distribution.

## References

* [W. Chung and S. Mascarenhas, *Modality, expected utility, and hypothesis testing*
  (2023)][chung-mascarenhas-2023]
* [N. Kolodny and J. MacFarlane, *Ifs and oughts* (2010)][kolodny-macfarlane-2010]
* [F. Cariani, M. Kaufmann and S. Kaufmann, *Deliberative modality under epistemic
  uncertainty* (2013)][cariani-kaufmann-kaufmann-2013]
* [A. Tversky and D. Kahneman, *Extensional Versus Intuitive Reasoning: The Conjunction
  Fallacy in Probability Judgment* (1983)][tversky-kahneman-1983]
* [D. Kahneman and A. Tversky, *On the psychology of prediction*
  (1973)][kahneman-tversky-1973]
-/

namespace ChungMascarenhas2023

open PMF PMF.Confirmation Conditionals.Probabilistic
open scoped ENNReal

variable {W : Type*} [Fintype W] {ι : Type*} [Fintype ι]

/-! ### The operators -/

/-- (6): `must φ` iff the expected `μ_R` given `φ` exceeds the threshold `θ` and no
alternative's does, `φ` being the only good-enough option or explanation. -/
def mustCM (p : PMF W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W))
    (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ ∧ ∀ ψ ∈ alts, sumLikelihoods p R ψ ≤ θ

/-- (17): `ought φ` iff `φ` is the best good-enough option, above `θ` and of strictly greater
expected value than every alternative. -/
def oughtCM (p : PMF W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W))
    (θ : ℝ≥0∞) : Prop :=
  sumLikelihoods p R φ > θ ∧
    ∀ ψ ∈ alts, sumLikelihoods p R ψ < sumLikelihoods p R φ

/-- §5: `mustCM` with the plausibility requirement of a reasonably high prior for the
prejacent, kept separate as the paper presents it as an add-on. -/
def mustCMWithPlausibility (p : PMF W) (R : ι → Set W) (φ : Set W)
    (alts : Set (Set W)) (θ θplaus : ℝ≥0∞) : Prop :=
  mustCM p R φ alts θ ∧ θplaus ≤ p.probOfSet φ

/-! ### Korean conditional evaluatives (§4) -/

/-- (48), left-hand side, the composition of `cip-ey iss-eya toy-n-ta`: Lassiter's threshold Θ
(46) applied to the conditional *if φ, then eval* ((45), `condIf` over `μ_R`), with the
*-(e)ya* exhaustifier negating each alternative's thresholded conditional. -/
def koreanConditionalEvaluative (p : PMF W) (R : ι → Set W) (φ : Set W)
    (alts : Set (Set W)) (θ : ℝ≥0∞) : Prop :=
  condIf p φ (countMeasure R) > θ ∧
    ∀ ψ ∈ alts, ¬(condIf p ψ (countMeasure R) > θ)

/-- (48): the Korean composition is the `must` semantics (6), by the identity
`condExpect_countMeasure` between the conditional's expected `μ_R` (45) and the sum of
likelihoods (12). -/
theorem koreanConditionalEvaluative_iff_mustCM (p : PMF W) (R : ι → Set W)
    (φ : Set W) (alts : Set (Set W)) (θ : ℝ≥0∞) :
    koreanConditionalEvaluative p R φ alts θ ↔ mustCM p R φ alts θ := by
  simp only [koreanConditionalEvaluative, mustCM, condIf,
    condExpect_countMeasure, not_lt]

/-! ### The miners puzzle (§3.1) -/

namespace Miners

/-- The six action-by-location worlds of Table 1: `0` block A with the miners in A, `1` block A
with them in B, `2` block B with them in A, `3` block B with them in B, `4` and `5` block
neither. -/
abbrev World := Fin 6

/-- Block shaft A. -/
def blockA : Set World := {w | w.val = 0 ∨ w.val = 1}
/-- Block shaft B. -/
def blockB : Set World := {w | w.val = 2 ∨ w.val = 3}
/-- Block neither shaft. -/
def blockNeither : Set World := {w | w.val = 4 ∨ w.val = 5}
/-- The miners are in shaft A. -/
def minersInA : Set World := {w | w.val = 0 ∨ w.val = 2 ∨ w.val = 4}
/-- The miners are in shaft B. -/
def minersInB : Set World := {w | w.val = 1 ∨ w.val = 3 ∨ w.val = 5}

/-- Miners saved at each world (Table 1): all ten at `0` and `3`, none at `1` and `2`, nine at
`4` and `5`. -/
def minersSaved : World → ℕ := fun w =>
  match w.val with
  | 0 => 10 | 1 => 0 | 2 => 0 | 3 => 10 | 4 => 9 | 5 => 9 | _ => 0

/-- The uniform prior: the locations equiprobable and independent of the action. -/
noncomputable def prior : PMF World := PMF.uniformOfFintype World

/-- (18), from [cariani-kaufmann-kaufmann-2013]: `R_D` = {one miner saved, …, ten miners saved},
an indexed family since distinct ideals coincide in extension on six worlds. -/
def idealsRD : Fin 10 → Set World := fun k => {w | k.val < minersSaved w}

instance : DecidablePred (· ∈ blockA) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 1))
instance : DecidablePred (· ∈ blockB) :=
  fun w => inferInstanceAs (Decidable (w.val = 2 ∨ w.val = 3))
instance : DecidablePred (· ∈ blockNeither) :=
  fun w => inferInstanceAs (Decidable (w.val = 4 ∨ w.val = 5))
instance : DecidablePred (· ∈ minersInA) :=
  fun w => inferInstanceAs (Decidable (w.val = 0 ∨ w.val = 2 ∨ w.val = 4))
instance : DecidablePred (· ∈ minersInB) :=
  fun w => inferInstanceAs (Decidable (w.val = 1 ∨ w.val = 3 ∨ w.val = 5))
instance (k : Fin 10) : DecidablePred (· ∈ idealsRD k) :=
  fun w => inferInstanceAs (Decidable (k.val < minersSaved w))

private instance {α : Type*} {s t : Set α} [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : DecidablePred (· ∈ (s ∩ t)) :=
  fun a => inferInstanceAs (Decidable (a ∈ s ∧ a ∈ t))

/-- `μ_{R_D}` counts miners saved: each world abides by exactly `minersSaved w` of the ten
ideals. -/
theorem countMeasure_idealsRD (w : World) :
    countMeasure idealsRD w = minersSaved w := by
  rw [countMeasure_apply, Nat.cast_inj]
  revert w; decide

private theorem ev_eval {φ : Set World} [DecidablePred (· ∈ φ)]
    [∀ i : Fin 10, DecidablePred (· ∈ (φ ∩ idealsRD i))] {m n : ℕ}
    (hm : (∑ i : Fin 10,
      (Finset.univ.filter (· ∈ φ ∩ idealsRD i)).card) = m)
    (hn : (Finset.univ.filter (· ∈ φ)).card = n) :
    sumLikelihoods prior idealsRD φ = (m : ℝ≥0∞) / n := by
  rw [prior, sumLikelihoods_uniformOfFintype, ← Nat.cast_sum, hm, hn]

/-- (19): blocking neither shaft has expected utility 9. -/
theorem ev_blockNeither : sumLikelihoods prior idealsRD blockNeither = 9 := by
  rw [ev_eval (by decide : _ = 18) (by decide : _ = 2),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (20): blocking shaft A has expected utility 5. -/
theorem ev_blockA : sumLikelihoods prior idealsRD blockA = 5 := by
  rw [ev_eval (by decide : _ = 10) (by decide : _ = 2),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (21): blocking shaft B has expected utility 5. -/
theorem ev_blockB : sumLikelihoods prior idealsRD blockB = 5 := by
  rw [ev_eval (by decide : _ = 10) (by decide : _ = 2),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (23): conditionalized on the miners being in A, blocking A has expected utility 10. -/
theorem ev_inA_blockA :
    sumLikelihoods prior idealsRD (minersInA ∩ blockA) = 10 := by
  rw [ev_eval (by decide : _ = 10) (by decide : _ = 1),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- Conditionalized on the miners being in A, blocking neither still has expected utility 9:
one miner drowns whatever their location. -/
theorem ev_inA_blockNeither :
    sumLikelihoods prior idealsRD (minersInA ∩ blockNeither) = 9 := by
  rw [ev_eval (by decide : _ = 9) (by decide : _ = 1),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- Conditionalized on the miners being in A, blocking B has expected utility 0. -/
theorem ev_inA_blockB :
    sumLikelihoods prior idealsRD (minersInA ∩ blockB) = 0 := by
  rw [ev_eval (by decide : _ = 0) (by decide : _ = 1),
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_add, ENNReal.add_eq_top, ENNReal.div_eq_top]
/-- (22): *we ought to block neither shaft*, for any `θ < 9`. -/
theorem ought_blockNeither {θ : ℝ≥0∞} (hθ : θ < 9) :
    oughtCM prior idealsRD blockNeither {blockA, blockB} θ := by
  refine ⟨ev_blockNeither ▸ hθ, ?_⟩
  rintro ψ (rfl | rfl)
  · rw [ev_blockA, ev_blockNeither]; norm_num
  · rw [ev_blockB, ev_blockNeither]; norm_num
/-- (24): *if the miners are in shaft A, we ought to block shaft A*, the if-clause
conditionalizing every expected utility on its antecedent (fn. 16, after Lassiter), for any
`θ < 10`. -/
theorem ought_if_inA_blockA {θ : ℝ≥0∞} (hθ : θ < 10) :
    oughtCM prior idealsRD (minersInA ∩ blockA)
      {minersInA ∩ blockNeither, minersInA ∩ blockB} θ := by
  refine ⟨ev_inA_blockA ▸ hθ, ?_⟩
  rintro ψ (rfl | rfl)
  · rw [ev_inA_blockNeither, ev_inA_blockA]; norm_num
  · rw [ev_inA_blockB, ev_inA_blockA]; norm_num
/-- (26): *we must block neither shaft* for `5 ≤ θ < 9`, blocking neither being the only
good-enough option. -/
theorem must_blockNeither {θ : ℝ≥0∞} (h5 : 5 ≤ θ) (h9 : θ < 9) :
    mustCM prior idealsRD blockNeither {blockA, blockB} θ := by
  refine ⟨ev_blockNeither ▸ h9, ?_⟩
  rintro ψ (rfl | rfl)
  · exact ev_blockA ▸ h5
  · exact ev_blockB ▸ h5

/-- (25b) as *must*: conditionalized on the miners being in A, blocking A is the only
good-enough option for `9 ≤ θ < 10`, blocking neither sitting at 9. -/
theorem must_if_inA_blockA {θ : ℝ≥0∞} (h9 : 9 ≤ θ) (h10 : θ < 10) :
    mustCM prior idealsRD (minersInA ∩ blockA)
      {minersInA ∩ blockNeither, minersInA ∩ blockB} θ := by
  refine ⟨ev_inA_blockA ▸ h10, ?_⟩
  rintro ψ (rfl | rfl)
  · exact ev_inA_blockNeither ▸ h9
  · exact ev_inA_blockB ▸ bot_le

/-- (26) needs `θ < 9` while (25b) needs `9 ≤ θ`: no single threshold verifies both *must*
claims. -/
theorem must_thresholds_incompatible :
    ¬ ∃ θ, mustCM prior idealsRD blockNeither {blockA, blockB} θ ∧
      mustCM prior idealsRD (minersInA ∩ blockA)
        {minersInA ∩ blockNeither, minersInA ∩ blockB} θ := by
  rintro ⟨θ, ⟨h9, -⟩, ⟨-, halts⟩⟩
  have h := halts _ (Set.mem_insert _ _)
  rw [ev_inA_blockNeither] at h
  rw [ev_blockNeither] at h9
  exact absurd (lt_of_le_of_lt h h9) (lt_irrefl _)

end Miners

/-! ### Modal Linda (§3.2) -/

namespace ModalLinda

/-- (30): `P(social justice ∣ teller) = 0.3`. -/
def prSocialJusticeGivenTeller : ℚ := 3 / 10
/-- (30): `P(anti-nuclear protests ∣ teller) = 0.2`. -/
def prAntiNuclearGivenTeller : ℚ := 2 / 10
/-- (31): `P(social justice ∣ feminist teller) = 0.8`. -/
def prSocialJusticeGivenFeministTeller : ℚ := 8 / 10
/-- (31): `P(anti-nuclear protests ∣ feminist teller) = 0.7`. -/
def prAntiNuclearGivenFeministTeller : ℚ := 7 / 10

/-- (32): `E[μ_R ∣ teller] = 0.5`. -/
def explanatoryValueTeller : ℚ :=
  prSocialJusticeGivenTeller + prAntiNuclearGivenTeller

/-- (33): `E[μ_R ∣ feminist teller] = 1.5`. -/
def explanatoryValueFeministTeller : ℚ :=
  prSocialJusticeGivenFeministTeller + prAntiNuclearGivenFeministTeller

/-- (34), the modal conjunction fallacy: for any threshold in `[1/2, 3/2)`, *Linda must be a
feminist bank teller* is true and *Linda must be a bank teller* false. -/
theorem modal_conjunction_fallacy {θ : ℚ} (h₀ : 1 / 2 ≤ θ) (h₁ : θ < 3 / 2) :
    explanatoryValueFeministTeller > θ ∧ explanatoryValueTeller ≤ θ :=
  ⟨by show (8 : ℚ) / 10 + 7 / 10 > θ; linarith,
   by show (3 : ℚ) / 10 + 2 / 10 ≤ θ; linarith⟩

end ModalLinda

/-! ### Modal Lawyers and Engineers (§3.3) -/

namespace ModalLawyers

/-- (37): `P(no interest in political and social issues ∣ engineer) = 0.78`. -/
def prNotPoliticalGivenEngineer : ℚ := 78 / 100
/-- (37): `P(enjoys mathematical puzzles ∣ engineer) = 0.55`. -/
def prMathGivenEngineer : ℚ := 55 / 100
/-- (38): `P(no interest in political and social issues ∣ lawyer) = 0.35`. -/
def prNotPoliticalGivenLawyer : ℚ := 35 / 100
/-- (38): `P(enjoys mathematical puzzles ∣ lawyer) = 0.28`. -/
def prMathGivenLawyer : ℚ := 28 / 100

/-- (39): `E[μ_R ∣ engineer] = 1.33`. -/
def explanatoryValueEngineer : ℚ :=
  prNotPoliticalGivenEngineer + prMathGivenEngineer

/-- (40): `E[μ_R ∣ lawyer] = 0.63`. -/
def explanatoryValueLawyer : ℚ :=
  prNotPoliticalGivenLawyer + prMathGivenLawyer

/-- (41), base-rate neglect: for any threshold in `[0.63, 1.33)`, *Jack must be an engineer*
is true whatever the prior split, explanatory value conditioning only on the hypotheses. -/
theorem base_rate_neglect {θ : ℚ} (h₀ : 63 / 100 ≤ θ) (h₁ : θ < 133 / 100) :
    explanatoryValueEngineer > θ ∧ explanatoryValueLawyer ≤ θ :=
  ⟨by show (78 : ℚ) / 100 + 55 / 100 > θ; linarith,
   by show (35 : ℚ) / 100 + 28 / 100 ≤ θ; linarith⟩

end ModalLawyers

end ChungMascarenhas2023
