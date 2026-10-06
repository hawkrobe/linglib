module

public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Core.MeasureTheory.Measure.Dirac

/-!
# Tsvilodub, Mulligan, Snider, Hawkins and Franke (2026): Act or Clarify? Modeling Sensitivity to Uncertainty and Cost in Communication

This file formalizes the computational model of [tsvilodub-etal-2026], a layered account of
when an agent asks a clarification question rather than acting under uncertainty. The decision
problem is the tuple ⟨G, P, R, U⟩ of two questioner goals, a prior placing probability ε on the
dispreferred goal, three direct answers, two mention-some answers and the exhaustive answer,
and utilities that make the matching mention-some answer worth 1 and the exhaustive answer
worth 1 − δ, `prior` and `utility`. The agent first decides whether to clarify, with a
probability that is a logistic function of the expected regret of the best action, `cqGate` and
`cqProb`; otherwise it acts by a softmax policy over goal-marginal expected utility, `policy`.
The mixture is `reaction`. The expected regret of a best action is the expected value of
perfect information of [raiffa-schlaifer-1961], `evpi_eq_expectedRegret`, and for the paper's
decision problem it is `min ε δ`, `evpi_eq_min`: uncertainty raises regret only while it stays below the cost of the
safe action, which is the interaction the paper tests. The exploratory predictions of
Experiment 1 then follow for every slope and threshold of the gate from the orderings of the
condition parameters alone: TL;JustAsk, `tl_justAsk`, NoNeedToAsk, `noNeedToAsk`, WorthAsking,
`worthAsking`, and their conjunction, `uncertainty_matters_most_when_costly`.

## Implementation notes

Regret, expected regret and the expected value of perfect information are defined for a utility
and a prior measure. The expected value of perfect information is the value of information of
observing the world, `evpi_eq_valueOfInformation`, so no clarification question is worth more
than it, `valueOfInformation_le_evpi`. The conditions are indexed by rational `ε` and `δ`, and
the prediction theorems assume `ε` is a probability. The policy is `RSA.speakerOfScore`, the
score speaker of the RSA kernel pipeline, applied to the goal-marginal expected utility; the model
has no listener. The
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

@[expose] public section

namespace TsvilodubEtAl2026

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Regret and the expected value of perfect information -/

section Regret

variable {W A : Type*} [MeasurableSpace W] (U : W → A → ℝ) (μ : Measure W)

/-- The best utility available at world `w`. -/
noncomputable def bestUtilityAt (w : W) : ℝ := ⨆ a, U w a

/-- The regret of action `a` at world `w` is what the best action at `w` earns over `a`. -/
noncomputable def regret (w : W) (a : A) : ℝ := bestUtilityAt U w - U w a

/-- The expected regret of action `a` averages its regret over the belief. -/
noncomputable def expectedRegret (a : A) : ℝ := ∫ w, regret U w a ∂μ

/-- The oracle value is the expected utility under perfect information. -/
noncomputable def oracleValue : ℝ := ∫ w, bestUtilityAt U w ∂μ

/-- The expected value of perfect information is the oracle value less the value of acting
now. -/
noncomputable def evpi : ℝ := oracleValue U μ - decisionValue U μ

variable {U μ} [Fintype W] [MeasurableSingletonClass W]

theorem expectedRegret_eq [IsFiniteMeasure μ] (a : A) :
    expectedRegret U μ a = oracleValue U μ - ∫ w, U w a ∂μ := by
  rw [expectedRegret, oracleValue, ← integral_sub .of_finite .of_finite]
  rfl

/-- The expected value of perfect information is the expected regret of a best action. -/
theorem evpi_eq_expectedRegret [IsFiniteMeasure μ] {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) : evpi U μ = expectedRegret U μ a := by
  rw [expectedRegret_eq, ha, evpi]

variable [StandardBorelSpace W] [Nonempty W] [IsProbabilityMeasure μ]

/-- The expected value of perfect information is the value of information of observing the
world. -/
theorem evpi_eq_valueOfInformation :
    evpi U μ = valueOfInformation (decisionValue U) Kernel.id μ := by
  show _ = valueOfInformation _ (Kernel.deterministic id measurable_id) μ
  rw [valueOfInformation_deterministic, evpi, oracleValue, integral_fintype .of_finite]
  congr 1
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Set.preimage_id, smul_eq_mul]
  rcases eq_or_ne (μ {w}) 0 with h | h
  · simp [measureReal_def, h]
  · have hδ : μ[|{w}] = Measure.dirac w := Measure.ext fun s hs ↦ by
      rw [cond_apply (measurableSet_singleton w), Measure.dirac_apply' _ hs]
      by_cases hw : w ∈ s
      · rw [Set.singleton_inter_of_mem hw, ENNReal.inv_mul_cancel h (measure_ne_top _ _),
          Set.indicator_of_mem hw, Pi.one_apply]
      · rw [Set.singleton_inter_eq_empty.2 hw, measure_empty, mul_zero,
          Set.indicator_of_notMem hw]
    simp [hδ, decisionValue, bestUtilityAt]

variable [Finite A]

theorem evpi_nonneg : 0 ≤ evpi U μ := by
  rw [evpi_eq_valueOfInformation]
  exact valueOfInformation_decisionValue_nonneg U _ μ

/-- No clarification question, and no experiment at all, is worth more than perfect
information. -/
theorem valueOfInformation_le_evpi {Y : Type*} [MeasurableSpace Y] [Finite Y]
    [MeasurableSingletonClass Y] (κ : Kernel W Y) [IsMarkovKernel κ] :
    valueOfInformation (decisionValue U) κ μ ≤ evpi U μ := by
  rw [evpi_eq_valueOfInformation]
  simpa only [Kernel.comp_id] using valueOfInformation_decisionValue_comp_le U Kernel.id μ κ

end Regret

/-! ### The decision problem ⟨G, P, R, U⟩ -/

/-- The questioner's goal. -/
inductive Goal where
  | g₁
  | g₂
  deriving DecidableEq, Repr, Fintype, Nonempty

instance : MeasurableSpace Goal := ⊤

instance : DiscreteMeasurableSpace Goal := ⟨fun _ ↦ trivial⟩

/-- A direct answer is one of the two mention-some answers or the exhaustive answer. -/
inductive Response where
  | ms1
  | ms2
  | exh
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Response := ⟨.exh⟩
instance : MeasurableSpace Response := ⊤

/-- The utilities of a condition with exhaustive-answer cost `δ`: a matching mention-some answer
is worth 1, a mismatching one 0, and the exhaustive answer `1 − δ` whatever the goal. -/
def utility (δ : ℚ) : Goal → Response → ℝ
  | .g₁, .ms1 => 1
  | .g₁, .ms2 => 0
  | .g₂, .ms1 => 0
  | .g₂, .ms2 => 1
  | _, .exh => 1 - δ

/-- The prior probability of each goal in a condition with uncertainty `ε`. -/
def goalWeight (ε : ℚ) : Goal → ℝ
  | .g₁ => 1 - ε
  | .g₂ => ε

/-- The prior of a condition with uncertainty `ε` puts probability `ε` on the dispreferred
goal. -/
noncomputable def prior (ε : ℚ) : Measure Goal :=
  ∑ g, ENNReal.ofReal (goalWeight ε g) • Measure.dirac g

/-- The expected utility of an answer in the condition `(ε, δ)`. -/
noncomputable def expectedUtility (ε δ : ℚ) (r : Response) : ℝ :=
  ∫ g, utility δ g r ∂prior ε

private theorem sum_goal {β : Type*} [AddCommMonoid β] (f : Goal → β) :
    (∑ g : Goal, f g) = f .g₁ + f .g₂ := by
  rw [show ∑ g, f g = f .g₁ + (f .g₂ + 0) from rfl, add_zero]

section Condition

variable {ε : ℚ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
include hε₀ hε₁

private theorem goalWeight_nonneg (g : Goal) : 0 ≤ goalWeight ε g := by
  have : (0 : ℝ) ≤ ε := by exact_mod_cast hε₀
  have : (ε : ℝ) ≤ 1 := by exact_mod_cast hε₁
  cases g <;> simp [goalWeight] <;> linarith

theorem isProbabilityMeasure_prior : IsProbabilityMeasure (prior ε) :=
  Measure.isProbabilityMeasure_sum_ofReal_smul_dirac (goalWeight_nonneg hε₀ hε₁)
    (by simp [sum_goal, goalWeight])

private theorem integral_prior (f : Goal → ℝ) :
    ∫ g, f g ∂prior ε = (1 - ε) * f .g₁ + ε * f .g₂ := by
  have := isProbabilityMeasure_prior hε₀ hε₁
  rw [integral_fintype .of_finite, sum_goal]
  simp only [prior, Measure.sum_ofReal_smul_dirac_real_apply (goalWeight_nonneg hε₀ hε₁),
    smul_eq_mul]
  simp [goalWeight]

theorem expectedUtility_ms1 (δ : ℚ) : expectedUtility ε δ .ms1 = 1 - ε := by
  rw [expectedUtility, integral_prior hε₀ hε₁]
  simp [utility]

theorem expectedUtility_ms2 (δ : ℚ) : expectedUtility ε δ .ms2 = ε := by
  rw [expectedUtility, integral_prior hε₀ hε₁]
  simp [utility]

theorem expectedUtility_exh (δ : ℚ) : expectedUtility ε δ .exh = 1 - δ := by
  rw [expectedUtility, integral_prior hε₀ hε₁]
  simp [utility]
  ring

end Condition

/-! ### The behavioral policy π = SoftMax(α · EU) -/

/-- The policy's score at the condition `(ε, δ)` is `α · EU(r)`. -/
noncomputable def policyScore (α : ℝ) (p : ℚ × ℚ) (r : Response) : EReal :=
  ((α * expectedUtility p.1 p.2 r : ℝ) : EReal)

/-- The behavioral policy, the softmax of `α · EU`, as a kernel from conditions to answers. -/
noncomputable def policy (α : ℝ) : Kernel (ℚ × ℚ) Response := RSA.speakerOfScore (policyScore α)

/-- Policy preference at a condition is comparison of expected utility. -/
theorem policy_real_singleton_lt_iff (α : ℝ) (p : ℚ × ℚ) (r r' : Response) :
    (policy α p).real {r} < (policy α p).real {r'} ↔ policyScore α p r < policyScore α p r' :=
  have htop : ∀ u, policyScore α p u ≠ ⊤ := fun _ ↦ EReal.coe_ne_top _
  have h0 : ∃ u, policyScore α p u ≠ ⊥ := ⟨.exh, EReal.coe_ne_bot _⟩
  RSA.speakerOfScore_real_singleton_lt_iff htop h0

private theorem policy_lt_policy {α : ℝ} (hα : 0 < α) {ε δ : ℚ} {r₁ r₂ : Response}
    (h : expectedUtility ε δ r₁ < expectedUtility ε δ r₂) :
    (policy α (ε, δ)).real {r₁} < (policy α (ε, δ)).real {r₂} := by
  rw [policy_real_singleton_lt_iff]
  exact EReal.coe_lt_coe (mul_lt_mul_of_pos_left h hα)

/-- Once uncertainty exceeds the cost of the exhaustive answer, the exhaustive answer beats
both mention-some answers. -/
theorem policy_prefers_exh_of_uncertain {α : ℝ} (hα : 0 < α) {ε δ : ℚ} (hδ : 0 ≤ δ)
    (h₁ : δ < ε) (h₂ : ε ≤ 1/2) :
    (policy α (ε, δ)).real {.ms1} < (policy α (ε, δ)).real {.exh} ∧
      (policy α (ε, δ)).real {.ms2} < (policy α (ε, δ)).real {.exh} := by
  have hε₀ : 0 ≤ ε := hδ.trans h₁.le
  have hε₁ : ε ≤ 1 := h₂.trans (by norm_num)
  have h₁' : (δ : ℝ) < ε := by exact_mod_cast h₁
  have h₂' : (ε : ℝ) ≤ 1/2 := by
    rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) by norm_num]; exact_mod_cast h₂
  exact ⟨policy_lt_policy hα (by
      rw [expectedUtility_ms1 hε₀ hε₁, expectedUtility_exh hε₀ hε₁]; linarith),
    policy_lt_policy hα (by
      rw [expectedUtility_ms2 hε₀ hε₁, expectedUtility_exh hε₀ hε₁]; linarith)⟩

/-- Under uncertainty below the cost of the exhaustive answer, the matching mention-some
answer wins. -/
theorem policy_prefers_ms1_of_confident {α : ℝ} (hα : 0 < α) {ε δ : ℚ} (hε₀ : 0 ≤ ε)
    (h₁ : ε < δ) (h₂ : ε < 1/2) :
    (policy α (ε, δ)).real {.exh} < (policy α (ε, δ)).real {.ms1} ∧
      (policy α (ε, δ)).real {.ms2} < (policy α (ε, δ)).real {.ms1} := by
  have hε₁ : ε ≤ 1 := h₂.le.trans (by norm_num)
  have h₁' : (ε : ℝ) < δ := by exact_mod_cast h₁
  have h₂' : (ε : ℝ) < 1/2 := by
    rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) by norm_num]; exact_mod_cast h₂
  exact ⟨policy_lt_policy hα (by
      rw [expectedUtility_exh hε₀ hε₁, expectedUtility_ms1 hε₀ hε₁]; linarith),
    policy_lt_policy hα (by
      rw [expectedUtility_ms2 hε₀ hε₁, expectedUtility_ms1 hε₀ hε₁]; linarith)⟩

/-! ### Expected regret of the best action -/

/-- The expected regret of the best action is `min ε δ`: regret is bounded by the uncertainty
and by the cost of the safe action, so uncertainty raises regret only while it stays below the
cost. -/
theorem evpi_eq_min {ε δ : ℚ} (hε₀ : 0 ≤ ε) (hε : ε ≤ 1/2) (hδ : 0 ≤ δ) :
    evpi (utility δ) (prior ε) = min ε δ := by
  have hε₁ : ε ≤ 1 := hε.trans (by norm_num)
  have := isProbabilityMeasure_prior hε₀ hε₁
  have hδ' : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hε' : (ε : ℝ) ≤ 1/2 := by
    rw [show (1/2 : ℝ) = ((1/2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hε
  have hb : BddAbove (Set.range fun r ↦ expectedUtility ε δ r) := (Set.finite_range _).bddAbove
  have hbest (g : Goal) : bestUtilityAt (utility δ) g = 1 := by
    refine le_antisymm (ciSup_le fun r ↦ ?_) ?_
    · cases g <;> cases r <;> simp [utility] <;> linarith
    · cases g
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove Response.ms1 (by simp [utility])
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove Response.ms2 (by simp [utility])
  have hvalue : decisionValue (utility δ) (prior ε) = 1 - min ε δ := by
    refine le_antisymm (ciSup_le fun r ↦ ?_) ?_
    · change expectedUtility ε δ r ≤ _
      have h₁ := min_le_left (ε : ℝ) δ
      have h₂ := min_le_right (ε : ℝ) δ
      cases r
      · rw [expectedUtility_ms1 hε₀ hε₁]; push_cast; linarith
      · rw [expectedUtility_ms2 hε₀ hε₁]; push_cast; linarith
      · rw [expectedUtility_exh hε₀ hε₁]; push_cast; linarith
    · rcases min_cases ε δ with ⟨hmin, _⟩ | ⟨hmin, _⟩
      · exact le_ciSup_of_le hb Response.ms1 (by
          change _ ≤ expectedUtility ε δ _; rw [expectedUtility_ms1 hε₀ hε₁, hmin])
      · exact le_ciSup_of_le hb Response.exh (by
          change _ ≤ expectedUtility ε δ _; rw [expectedUtility_exh hε₀ hε₁, hmin])
  rw [evpi, oracleValue, hvalue]
  simp [hbest]

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

/-- The probability of clarifying at the condition `(ε, δ)` is the gate applied to the expected
regret of the best action. -/
noncomputable def cqProb (τ c : ℝ) (ε δ : ℚ) : ℝ :=
  cqGate τ c (evpi (utility δ) (prior ε))

/-! ### The predictions for Experiment 1 -/

/-- In TL;JustAsk, when the exhaustive answer costs more than the low uncertainty, as in a large
option space, higher uncertainty means more clarification. -/
theorem tl_justAsk {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {εL εH δ : ℚ} (hδ : 0 ≤ δ) (hL₀ : 0 ≤ εL)
    (hε : εL < εH) (hH : εH ≤ 1/2) (hL : εL < δ) : cqProb τ c εL δ < cqProb τ c εH δ := by
  rw [cqProb, cqProb, evpi_eq_min hL₀ (hε.le.trans hH) hδ, evpi_eq_min (hL₀.trans hε.le) hH hδ,
    min_eq_left hL.le]
  exact cqGate_strictMono hτ c (by exact_mod_cast lt_min hε hL)

/-- In NoNeedToAsk, when the exhaustive answer costs less than either uncertainty, as in a small
option space, uncertainty makes no difference to clarification, the regret signal being capped
at the cost in both conditions. -/
theorem noNeedToAsk (τ c : ℝ) {εL εH δ : ℚ} (hδ : 0 ≤ δ) (hL : δ ≤ εL) (hH : δ ≤ εH)
    (hεL : εL ≤ 1/2) (hεH : εH ≤ 1/2) : cqProb τ c εL δ = cqProb τ c εH δ := by
  rw [cqProb, cqProb, evpi_eq_min (hδ.trans hL) hεL hδ, evpi_eq_min (hδ.trans hH) hεH hδ,
    min_eq_right hL, min_eq_right hH]

/-- In WorthAsking, at an uncertainty above the smaller cost, a costlier exhaustive answer means
more clarification. -/
theorem worthAsking {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {ε δS δL : ℚ} (hε : ε ≤ 1/2) (hS : 0 ≤ δS)
    (hεS : δS < ε) (hδ : δS < δL) : cqProb τ c ε δS < cqProb τ c ε δL := by
  rw [cqProb, cqProb, evpi_eq_min (hS.trans hεS.le) hε hS,
    evpi_eq_min (hS.trans hεS.le) hε (hS.trans hδ.le), min_eq_right hεS.le]
  exact cqGate_strictMono hτ c (by exact_mod_cast lt_min hεS hδ)

/-- Uncertainty raises clarification when the exhaustive answer is costly and leaves it unchanged
when it is cheap, the interaction the paper tests. -/
theorem uncertainty_matters_most_when_costly {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {εL εH δS δL : ℚ}
    (hS : 0 ≤ δS) (hSL : δS ≤ εL) (hε : εL < εH) (hH : εH ≤ 1/2) (hL : εL < δL) :
    cqProb τ c εL δS = cqProb τ c εH δS ∧ cqProb τ c εL δL < cqProb τ c εH δL :=
  ⟨noNeedToAsk τ c hS hSL (hSL.trans hε.le) (hε.le.trans hH) hH,
   tl_justAsk hτ c (hS.trans (hSL.trans hL.le)) (hS.trans hSL) hε hH hL⟩

/-! ### The layered reaction -/

/-- A reaction either clarifies or commits to a direct answer. -/
inductive Reaction where
  | cq
  | act (r : Response)
  deriving DecidableEq, Repr

instance : MeasurableSpace Reaction := ⊤

/-- The layered mixture clarifies with probability `q` and otherwise acts by the policy `pol`. -/
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

/-- The reaction at the condition `(ε, δ)` gates by the logistic of the expected regret, then
acts by the softmax policy. -/
noncomputable def reaction (τ c α : ℝ) (ε δ : ℚ) : Measure Reaction :=
  layered (ENNReal.ofReal (cqProb τ c ε δ)) (policy α (ε, δ))

theorem reaction_apply_cq (τ c α : ℝ) (ε δ : ℚ) :
    reaction τ c α ε δ {.cq} = ENNReal.ofReal (cqProb τ c ε δ) :=
  layered_apply_cq _ _

end TsvilodubEtAl2026
