import Linglib.Pragmatics.RSA.Basic
import Linglib.Core.Probability.Decision.Basic

/-!
# Tsvilodub, Mulligan, Snider, Hawkins and Franke (2026): Act or Clarify? Modeling Sensitivity to Uncertainty and Cost in Communication

This file formalizes the computational model of [tsvilodub-etal-2026], a layered account of
when an agent asks a clarification question rather than acting under uncertainty. The decision
problem is the tuple ⟨G, P, R, U⟩ of two questioner goals, a prior placing probability ε on the
dispreferred goal, three direct answers, two mention-some answers and the exhaustive answer,
and utilities that make the matching mention-some answer worth 1 and the exhaustive answer
worth 1 − δ, `problem`. The agent first decides whether to clarify, with a probability that is a
logistic function of the expected regret of the best action, `cqGate` and `cqProb`; otherwise
it acts by a softmax policy over goal-marginal expected utility, `policy`. The mixture is
`reaction`. The expected regret of a best action is the expected value of perfect information
of [raiffa-schlaifer-1961], `evpi_eq_expectedRegret`, and for the paper's decision problem it is
`min ε δ`, `evpi_eq_min`: uncertainty raises regret only while it stays below the cost of the
safe action, which is the interaction the paper tests. The exploratory predictions of
Experiment 1 then follow for every slope and threshold of the gate from the orderings of the
condition parameters alone: TL;JustAsk, `tl_justAsk`, NoNeedToAsk, `noNeedToAsk`, WorthAsking,
`worthAsking`, and their conjunction, `uncertainty_matters_most_when_costly`.

## Implementation notes

Regret, expected regret and the expected value of perfect information are defined over the
substrate's `Core.DecisionTheory.DecisionProblem`. The expected value of perfect information is
the utility value of the finest question in the sense of [van-rooy-2003],
`evpi_eq_questionUtility_bot`, so no clarification question is worth more than it,
`questionUtility_le_evpi`. The policy is `RSA.speakerOfScore`, the score speaker of the RSA
kernel pipeline, applied to the goal-marginal expected utility; the model has no listener. The
utilities follow [hawkins-etal-2025]. The fitted posterior means of Experiment 1, ε of 0.17 and
0.49 for low and high uncertainty, δ of 0.11 and 0.32 for small and large option spaces, a slope
τ of 3.60 and a threshold c of 0.18, enter only through the orderings δ_S < ε_L < δ_L < ε_H ≤ 1/2
that the prediction theorems assume. JustListThemAll and TooManyToList, the predictions about
exhaustive answers, concern the policy's mass on the exhaustive answer across conditions and
are stated within a condition only, `policy_prefers_exh_of_uncertain` and
`policy_prefers_ms1_of_confident`. Experiment 2, on reactions to directives, is not modelled in
the paper: it found a binarized effect of uncertainty on clarification questions, a gradient
effect on direct action, and more clarification when errors are costly, and the paper leaves a
common utility scale for linguistic and non-linguistic actions to future work. The comparison
with the ablated models, without cost, without uncertainty, or with an expectation of regret
over all responses, is a model-fitting result and is not formalized.

## References

* [tsvilodub-etal-2026]
* [raiffa-schlaifer-1961]
* [van-rooy-2003]
* [hawkins-etal-2025]
-/

namespace TsvilodubEtAl2026

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Core.DecisionTheory Core.DecisionTheory.DecisionProblem

/-! ### Regret and the expected value of perfect information -/

section Regret

variable {W A : Type*} (dp : DecisionProblem ℚ W A) (actions : Finset A)

/-- The best utility available at world `w`, or `0` when there are no actions. -/
def bestUtilityAt (w : W) : ℚ :=
  if h : actions.Nonempty then actions.sup' h (dp.utility w) else 0

/-- The regret of action `a` at world `w`: what the best action at `w` earns over `a`. -/
def regret (w : W) (a : A) : ℚ := bestUtilityAt dp actions w - dp.utility w a

variable {dp actions}

theorem utility_le_bestUtilityAt (hne : actions.Nonempty) {a : A} (ha : a ∈ actions) (w : W) :
    dp.utility w a ≤ bestUtilityAt dp actions w := by
  rw [bestUtilityAt, dite_eq_left hne]
  exact Finset.le_sup' _ ha

private theorem condExpectedUtility_singleton {w : W} (h : dp.prior w ≠ 0) (a : A) :
    dp.condExpectedUtility {w} a = dp.utility w a := by
  simp only [condExpectedUtility, Finset.sum_singleton, ite_eq_right h, div_self h, one_mul]

private theorem prior_mul_condValue_singleton (w : W) :
    dp.prior w * dp.condValue actions {w} = dp.prior w * bestUtilityAt dp actions w := by
  by_cases h : dp.prior w = 0
  · simp [h]
  · unfold condValue bestUtilityAt
    split_ifs
    · congr 2
      funext a
      exact condExpectedUtility_singleton h a
    · rfl

variable (dp actions) [Fintype W]

/-- The expected regret of action `a`. -/
def expectedRegret (a : A) : ℚ := ∑ w, dp.prior w * regret dp actions w a

/-- The oracle value: expected utility under perfect information. -/
def oracleValue : ℚ := ∑ w, dp.prior w * bestUtilityAt dp actions w

/-- The expected value of perfect information: the oracle value less the value of acting now. -/
def evpi : ℚ := oracleValue dp actions - dp.value actions

variable {dp actions}

theorem expectedRegret_eq (a : A) :
    expectedRegret dp actions a = oracleValue dp actions - dp.expectedUtility a := by
  simp only [expectedRegret, regret, oracleValue, expectedUtility, mul_sub,
    Finset.sum_sub_distrib]

/-- The expected value of perfect information is the expected regret of a best action. -/
theorem evpi_eq_expectedRegret {a : A} (ha : dp.expectedUtility a = dp.value actions) :
    evpi dp actions = expectedRegret dp actions a := by
  rw [expectedRegret_eq, ha, evpi]

theorem value_le_oracleValue (hprior : ∀ w, 0 ≤ dp.prior w) (hne : actions.Nonempty) :
    dp.value actions ≤ oracleValue dp actions := by
  rw [value_of_nonempty hne]
  exact Finset.sup'_le _ _ λ a ha => Finset.sum_le_sum λ w _ =>
    mul_le_mul_of_nonneg_left (utility_le_bestUtilityAt hne ha w) (hprior w)

theorem evpi_nonneg (hprior : ∀ w, 0 ≤ dp.prior w) (hne : actions.Nonempty) :
    0 ≤ evpi dp actions :=
  sub_nonneg.2 (value_le_oracleValue hprior hne)

/-- The expected value of perfect information is the utility value of the finest question, the
partition of the worlds into singletons. -/
theorem evpi_eq_questionUtility_bot [DecidableEq W] (hsum : ∑ w, dp.prior w = 1) :
    evpi dp actions =
      dp.questionUtility actions (⊥ : Finpartition (Finset.univ : Finset W)).parts := by
  simp only [questionUtility, Finpartition.parts_bot, Finset.sum_map, Function.Embedding.coeFn_mk,
    cellProbability, Finset.sum_singleton, utilityValue, mul_sub, prior_mul_condValue_singleton,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, evpi, oracleValue]

/-- No question is worth more than perfect information. -/
theorem questionUtility_le_evpi [DecidableEq W] (hprior : ∀ w, 0 ≤ dp.prior w)
    (hsum : ∑ w, dp.prior w = 1) (P : Finpartition (Finset.univ : Finset W)) :
    dp.questionUtility actions P.parts ≤ evpi dp actions :=
  (evpi_eq_questionUtility_bot hsum).symm ▸ questionUtility_anti_of_le dp actions bot_le hprior

end Regret

/-! ### The decision problem ⟨G, P, R, U⟩ -/

/-- The questioner's goal. -/
inductive Goal where
  | g₁
  | g₂
  deriving DecidableEq, Repr, Fintype, Nonempty

instance : MeasurableSpace Goal := ⊤

/-- The direct answers: the two mention-some answers and the exhaustive answer. -/
inductive Response where
  | ms1
  | ms2
  | exh
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Response := ⟨.exh⟩
instance : MeasurableSpace Response := ⊤

/-- The decision problem of a condition with uncertainty `ε` and exhaustive-answer cost `δ`:
the dispreferred goal has probability `ε`, a matching mention-some answer is worth 1, a
mismatching one 0, and the exhaustive answer `1 − δ` whatever the goal. -/
def problem (ε δ : ℚ) : DecisionProblem ℚ Goal Response where
  utility
    | .g₁, .ms1 => 1
    | .g₁, .ms2 => 0
    | .g₂, .ms1 => 0
    | .g₂, .ms2 => 1
    | _, .exh => 1 - δ
  prior
    | .g₁ => 1 - ε
    | .g₂ => ε

private theorem sum_goal {β : Type*} [AddCommMonoid β] (f : Goal → β) :
    (∑ g : Goal, f g) = f .g₁ + f .g₂ := by
  rw [show ∑ g, f g = f .g₁ + (f .g₂ + 0) from rfl, add_zero]

theorem expectedUtility_ms1 (ε δ : ℚ) : (problem ε δ).expectedUtility .ms1 = 1 - ε := by
  simp only [expectedUtility, sum_goal, problem]; ring

theorem expectedUtility_ms2 (ε δ : ℚ) : (problem ε δ).expectedUtility .ms2 = ε := by
  simp only [expectedUtility, sum_goal, problem]; ring

theorem expectedUtility_exh (ε δ : ℚ) : (problem ε δ).expectedUtility .exh = 1 - δ := by
  simp only [expectedUtility, sum_goal, problem]; ring

/-! ### The behavioral policy π = SoftMax(α · EU) -/

/-- The policy's score, `α · EU(r)`, at the condition `(ε, δ)`. -/
noncomputable def policyScore (α : ℝ) (p : ℚ × ℚ) (r : Response) : EReal :=
  ((α * ((problem p.1 p.2).expectedUtility r : ℝ) : ℝ) : EReal)

/-- The behavioral policy, the softmax of `α · EU`, as a kernel from conditions to answers. -/
noncomputable def policy (α : ℝ) : Kernel (ℚ × ℚ) Response := RSA.speakerOfScore (policyScore α)

/-- Policy preference at a condition is comparison of expected utility. -/
theorem policy_real_singleton_lt_iff (α : ℝ) (p : ℚ × ℚ) (r r' : Response) :
    (policy α p).real {r} < (policy α p).real {r'} ↔ policyScore α p r < policyScore α p r' :=
  have htop : ∀ u, policyScore α p u ≠ ⊤ := λ _ => EReal.coe_ne_top _
  have h0 : ∃ u, policyScore α p u ≠ ⊥ := ⟨.exh, EReal.coe_ne_bot _⟩
  RSA.speakerOfScore_real_singleton_lt_iff htop h0

private theorem policy_lt_policy {α : ℝ} (hα : 0 < α) {ε δ : ℚ} {r₁ r₂ : Response}
    (h : (problem ε δ).expectedUtility r₁ < (problem ε δ).expectedUtility r₂) :
    (policy α (ε, δ)).real {r₁} < (policy α (ε, δ)).real {r₂} := by
  rw [policy_real_singleton_lt_iff]
  exact EReal.coe_lt_coe (mul_lt_mul_of_pos_left (by exact_mod_cast h) hα)

/-- Once uncertainty exceeds the cost of the exhaustive answer, the exhaustive answer beats
both mention-some answers. -/
theorem policy_prefers_exh_of_uncertain {α : ℝ} (hα : 0 < α) {ε δ : ℚ} (h₁ : δ < ε)
    (h₂ : ε ≤ 1/2) :
    (policy α (ε, δ)).real {.ms1} < (policy α (ε, δ)).real {.exh} ∧
      (policy α (ε, δ)).real {.ms2} < (policy α (ε, δ)).real {.exh} :=
  ⟨policy_lt_policy hα (by rw [expectedUtility_ms1, expectedUtility_exh]; linarith),
   policy_lt_policy hα (by rw [expectedUtility_ms2, expectedUtility_exh]; linarith)⟩

/-- Under uncertainty below the cost of the exhaustive answer, the matching mention-some
answer wins. -/
theorem policy_prefers_ms1_of_confident {α : ℝ} (hα : 0 < α) {ε δ : ℚ} (h₁ : ε < δ)
    (h₂ : ε < 1/2) :
    (policy α (ε, δ)).real {.exh} < (policy α (ε, δ)).real {.ms1} ∧
      (policy α (ε, δ)).real {.ms2} < (policy α (ε, δ)).real {.ms1} :=
  ⟨policy_lt_policy hα (by rw [expectedUtility_exh, expectedUtility_ms1]; linarith),
   policy_lt_policy hα (by rw [expectedUtility_ms2, expectedUtility_ms1]; linarith)⟩

/-! ### Expected regret of the best action -/

private theorem bestUtilityAt_problem {ε δ : ℚ} (hδ : 0 ≤ δ) (g : Goal) :
    bestUtilityAt (problem ε δ) Finset.univ g = 1 := by
  rw [bestUtilityAt, dite_eq_left Finset.univ_nonempty]
  refine le_antisymm (Finset.sup'_le _ _ λ r _ => ?_) ?_
  · cases g <;> cases r <;> simp [problem] <;> linarith
  · cases g
    · exact Finset.le_sup' (α := ℚ) ((problem ε δ).utility .g₁) (Finset.mem_univ .ms1)
    · exact Finset.le_sup' (α := ℚ) ((problem ε δ).utility .g₂) (Finset.mem_univ .ms2)

private theorem oracleValue_problem {ε δ : ℚ} (hδ : 0 ≤ δ) :
    oracleValue (problem ε δ) Finset.univ = 1 := by
  rw [oracleValue, sum_goal, bestUtilityAt_problem hδ, bestUtilityAt_problem hδ]
  show (1 - ε) * 1 + ε * 1 = 1
  ring

private theorem value_problem {ε δ : ℚ} (hε : ε ≤ 1/2) :
    (problem ε δ).value Finset.univ = 1 - min ε δ := by
  rw [value_of_nonempty Finset.univ_nonempty]
  refine le_antisymm (Finset.sup'_le _ _ λ r _ => ?_) ?_
  · have h₁ := min_le_left ε δ
    have h₂ := min_le_right ε δ
    cases r
    · rw [expectedUtility_ms1]; linarith
    · rw [expectedUtility_ms2]; linarith
    · rw [expectedUtility_exh]; linarith
  · rcases min_cases ε δ with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · calc 1 - min ε δ = (problem ε δ).expectedUtility .ms1 := by rw [expectedUtility_ms1, hmin]
        _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ Response.ms1)
    · calc 1 - min ε δ = (problem ε δ).expectedUtility .exh := by rw [expectedUtility_exh, hmin]
        _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ Response.exh)

/-- The expected regret of the best action is `min ε δ`: regret is bounded by the uncertainty
and by the cost of the safe action, so uncertainty raises regret only while it stays below the
cost. -/
theorem evpi_eq_min {ε δ : ℚ} (hε : ε ≤ 1/2) (hδ : 0 ≤ δ) :
    evpi (problem ε δ) Finset.univ = min ε δ := by
  rw [evpi, oracleValue_problem hδ, value_problem hε]
  ring

/-! ### The clarification gate -/

/-- The logistic gate with slope `τ` and threshold `c` on the regret signal `x`. -/
noncomputable def cqGate (τ c x : ℝ) : ℝ := (1 + Real.exp (-(τ * (x - c))))⁻¹

theorem cqGate_pos (τ c x : ℝ) : 0 < cqGate τ c x := by
  rw [cqGate]
  positivity

theorem cqGate_le_one (τ c x : ℝ) : cqGate τ c x ≤ 1 := by
  rw [cqGate, inv_le_one_iff₀]
  exact .inr (by linarith [Real.exp_pos (-(τ * (x - c)))])

/-- The gate is strictly increasing in expected regret: the more there is to lose by acting,
the more clarification. -/
theorem cqGate_strictMono {τ : ℝ} (hτ : 0 < τ) (c : ℝ) : StrictMono (cqGate τ c) := by
  intro x y hxy
  rw [cqGate, cqGate]
  have hexp : Real.exp (-(τ * (y - c))) < Real.exp (-(τ * (x - c))) :=
    Real.exp_lt_exp.2 (by nlinarith)
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (by linarith)

/-- The probability of clarifying at the condition `(ε, δ)`: the gate applied to the expected
regret of the best action. -/
noncomputable def cqProb (τ c : ℝ) (ε δ : ℚ) : ℝ :=
  cqGate τ c ((evpi (problem ε δ) Finset.univ : ℚ) : ℝ)

/-! ### The predictions for Experiment 1 -/

/-- TL;JustAsk: when the exhaustive answer costs more than the low uncertainty, as in a large
option space, higher uncertainty means more clarification. -/
theorem tl_justAsk {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {εL εH δ : ℚ} (hδ : 0 ≤ δ) (hε : εL < εH)
    (hH : εH ≤ 1/2) (hL : εL < δ) : cqProb τ c εL δ < cqProb τ c εH δ := by
  rw [cqProb, cqProb, evpi_eq_min (hε.le.trans hH) hδ, evpi_eq_min hH hδ, min_eq_left hL.le]
  exact cqGate_strictMono hτ c (by exact_mod_cast lt_min hε hL)

/-- NoNeedToAsk: when the exhaustive answer costs less than either uncertainty, as in a small
option space, uncertainty makes no difference to clarification, the regret signal being capped
at the cost in both conditions. -/
theorem noNeedToAsk (τ c : ℝ) {εL εH δ : ℚ} (hδ : 0 ≤ δ) (hL : δ ≤ εL) (hH : δ ≤ εH)
    (hεL : εL ≤ 1/2) (hεH : εH ≤ 1/2) : cqProb τ c εL δ = cqProb τ c εH δ := by
  rw [cqProb, cqProb, evpi_eq_min hεL hδ, evpi_eq_min hεH hδ, min_eq_right hL, min_eq_right hH]

/-- WorthAsking: at an uncertainty above the smaller cost, a costlier exhaustive answer means
more clarification. -/
theorem worthAsking {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {ε δS δL : ℚ} (hε : ε ≤ 1/2) (hS : 0 ≤ δS)
    (hεS : δS < ε) (hδ : δS < δL) : cqProb τ c ε δS < cqProb τ c ε δL := by
  rw [cqProb, cqProb, evpi_eq_min hε hS, evpi_eq_min hε (hS.trans hδ.le), min_eq_right hεS.le]
  exact cqGate_strictMono hτ c (by exact_mod_cast lt_min hεS hδ)

/-- The interaction: uncertainty raises clarification when the exhaustive answer is costly and
leaves it unchanged when it is cheap. -/
theorem uncertainty_matters_most_when_costly {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {εL εH δS δL : ℚ}
    (hS : 0 ≤ δS) (hSL : δS ≤ εL) (hε : εL < εH) (hH : εH ≤ 1/2) (hL : εL < δL) :
    cqProb τ c εL δS = cqProb τ c εH δS ∧ cqProb τ c εL δL < cqProb τ c εH δL :=
  ⟨noNeedToAsk τ c hS hSL (hSL.trans hε.le) (hε.le.trans hH) hH,
   tl_justAsk hτ c (hS.trans (hSL.trans hL.le)) hε hH hL⟩

/-! ### The layered reaction -/

/-- A reaction: clarify, or commit to a direct answer. -/
inductive Reaction where
  | cq
  | act (r : Response)
  deriving DecidableEq, Repr

instance : MeasurableSpace Reaction := ⊤

/-- The layered mixture: clarify with probability `q`, otherwise act by the policy `pol`. -/
noncomputable def layered (q : ℝ≥0∞) (pol : Measure Response) : Measure Reaction :=
  (1 - q) • pol.map Reaction.act + q • Measure.dirac .cq

theorem layered_apply_cq (q : ℝ≥0∞) (pol : Measure Response) : layered q pol {.cq} = q := by
  rw [layered, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, Measure.map_apply .of_discrete (.singleton _),
    show Reaction.act ⁻¹' {Reaction.cq} = ∅ from by ext r; simp, measure_empty, mul_zero,
    Measure.dirac_apply_of_mem (Set.mem_singleton _), mul_one, zero_add]

theorem layered_apply_act (q : ℝ≥0∞) (pol : Measure Response) (r : Response) :
    layered q pol {.act r} = (1 - q) * pol {r} := by
  rw [layered, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, Measure.map_apply .of_discrete (.singleton _),
    show Reaction.act ⁻¹' {Reaction.act r} = {r} from by ext r'; simp,
    Measure.dirac_apply' _ (.singleton _), Set.indicator_of_notMem (by simp), mul_zero, add_zero]

/-- The reaction at the condition `(ε, δ)`: gate by the logistic of the expected regret, then
act by the softmax policy. -/
noncomputable def reaction (τ c α : ℝ) (ε δ : ℚ) : Measure Reaction :=
  layered (ENNReal.ofReal (cqProb τ c ε δ)) (policy α (ε, δ))

theorem reaction_apply_cq (τ c α : ℝ) (ε δ : ℚ) :
    reaction τ c α ε δ {.cq} = ENNReal.ofReal (cqProb τ c ε δ) :=
  layered_apply_cq _ _

end TsvilodubEtAl2026
