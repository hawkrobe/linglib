import Linglib.Pragmatics.RSA.Canonical
import Linglib.Core.Probability.Decision.Basic
import Linglib.Core.Probability.Constructions
import Linglib.Studies.DongEtAl2026PMF
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# [tsvilodub-etal-2026] — Act or Clarify? Uncertainty and cost in communication

When should an agent ask a clarification question (CQ) rather than act under
uncertainty? [tsvilodub-etal-2026] predict and confirm that CQ rates depend
on contextual uncertainty (ε) about the interlocutor's goal and the cost (δ)
of safe actions, interacting: uncertainty matters most when acting
incorrectly is costly.

The paper's computational model is **layered decision theory, not RSA**: a
decision problem `⟨G, P, R, U⟩` with `P(g₂) = ε` and exhaustive-answer
utility `1 − δ`; a behavioral policy `π = SoftMax(α · EU)` over the
**goal-marginal** expected utility `EU(r) = Σ_g P(g)·U(g,r)`; and a CQ gate
`P(r_cq) = Logistic(τ · (ExpRegret(r*) − c))`, where `ExpRegret(r*)` is the
expected regret of the best action — the expected value of perfect
information ([raiffa-schlaifer-1961]). This file formalises all three
layers, building on `Core.DecisionTheory.DecisionProblem`; `evpi` below
identifies the paper's ExpRegret with EVPI.

## Main statements

* `evpi_eq_min` — for the paper's decision problem the expected regret of
  the best action has the closed form `min ε δ`: the uncertainty/cost
  interaction in one equation.
* `policy_prefers_exh_of_uncertain` / `policy_prefers_ms1_of_confident` —
  the behavioral policy flips from the matching mention-some to the safe
  exhaustive answer as uncertainty crosses cost (`δ < ε`).
* `tl_justAsk`, `noNeedToAsk`, `worthAsking`,
  `uncertainty_matters_most_when_costly` — the gate-level predictions, for
  *every* `τ > 0` and threshold `c` (`noNeedToAsk` is an exact equality,
  the paper's null prediction).
* `reaction` — the layered mixture: clarify with the gate probability,
  otherwise act by `policy`.
* `L1_exh_transmits_prior` etc. — an **RSA reinterpretation** (this file's
  extension, *not* the paper's model): the goal-conditioned speaker — the
  ε → 0 / post-clarification limit of `π`, [hawkins-etal-2025]'s
  action-utility respondent R₁ at β = 1, w_c = 0 — inverted by a Bayesian
  listener. The paper's model contains no listener.

## Implementation notes

Parameter provenance (Bayesian posterior means fitted to Exp 1): δ_L = 0.32,
δ_S = 0.11 (large/small option space), ε_H = 0.49, ε_L = 0.17 (high/low
uncertainty), τ = 3.60, c = 0.18. The gate-level prediction theorems hold
for all `τ > 0` and `c`, so the fitted values matter only through the
orderings `δ_S < ε_L < δ_L < ε_H ≤ 1/2`. In the RSA section `exhVal = 1 − δ`
and the priors 83 : 17 and 51 : 49 are `(1 − ε) : ε`; α = 1 there is this
file's choice (the paper's α has prior N(5, 1)) — the strict-preference
theorems are stated for any α > 0.
-/

set_option autoImplicit false

namespace TsvilodubEtAl2026

open scoped ENNReal NNReal
open Core.DecisionTheory Core.DecisionTheory.DecisionProblem

/-! ### Expected value of perfect information

[raiffa-schlaifer-1961]'s EVPI over a `Core.DecisionTheory.DecisionProblem`:
the gap between the oracle value (expected utility under perfect
information) and the value of acting now. EVPI is the maximum possible
`questionUtility` ([van-rooy-2003]) — it equals `questionUtility` on the
identity partition, so any specific clarification question yields at most
EVPI; it is the paper's `ExpRegret(r*)` and the upper bound on
[dong-etal-2026]'s VoI. -/

/-- Maximum utility achievable at world `w` across actions.

    With Finset actions, this is `sup'` over utilities at world `w`. -/
def bestUtilityAt {W A : Type*} (dp : DecisionProblem ℚ W A)
    (actions : Finset A) (w : W) : ℚ :=
  if h : actions.Nonempty then actions.sup' h (dp.utility w) else 0

/-- Oracle value: expected utility under perfect information.
    `Σ_w P(w) · max_a U(w, a)` -/
def oracleValue {W A : Type*} [Fintype W] (dp : DecisionProblem ℚ W A)
    (actions : Finset A) : ℚ :=
  ∑ w : W, dp.prior w * bestUtilityAt dp actions w

/-- Expected value of perfect information (EVPI).

    EVPI = oracleValue − DecisionProblem.value
         = Σ_w P(w) · max_a U(w,a) − max_a Σ_w P(w) · U(w,a)

    Equivalently, the expected regret of the current best action.

    [raiffa-schlaifer-1961] -/
def evpi {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem ℚ W A) (actions : Finset A) : ℚ :=
  oracleValue dp actions - DecisionProblem.value dp actions

/-- EVPI is non-negative: acting with perfect information is at least
    as good as acting without.

    Proof sketch: For each action `a`, its expected utility `EU(a)` equals
    `Σ_w P(w) · U(w,a)`. The oracle value `Σ_w P(w) · max_a' U(w,a')`
    is pointwise ≥ `Σ_w P(w) · U(w,a)` since `max_a' U(w,a') ≥ U(w,a)`.
    Therefore `oracleValue ≥ EU(a)` for every `a`, hence
    `oracleValue ≥ max_a EU(a) = DecisionProblem.value`. -/
theorem evpi_nonneg {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem ℚ W A) (actions : Finset A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hne : actions.Nonempty) :
    0 ≤ evpi dp actions := by
  unfold evpi
  suffices h : DecisionProblem.value dp actions ≤ oracleValue dp actions by linarith
  -- DecisionProblem.value = sup' of expectedUtility; show each EU(a) ≤ oracleValue
  unfold DecisionProblem.value oracleValue
  rw [dif_pos hne]
  apply Finset.sup'_le
  intro a ha
  -- EU(a) = Σ_w P(w) · U(w,a) ≤ Σ_w P(w) · bestUtilityAt w
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_of_nonneg_left _ (hprior w)
  -- U(w,a) ≤ bestUtilityAt w
  unfold bestUtilityAt
  rw [dif_pos hne]
  exact Finset.le_sup' _ ha

/-! ### The decision problem ⟨G, P, R, U⟩ -/

/-- The questioner's latent goal. -/
inductive Goal where | g₁ | g₂
  deriving DecidableEq, Repr, Fintype

/-- Available non-CQ responses: targeted mention-some answers and the safe
exhaustive answer. -/
inductive Response where
  | ms1 | ms2
  | exh  -- reliable but costly
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Response := ⟨.exh⟩

/-- The paper's parameterized decision problem: `P(g₂) = ε` (uncertainty),
matching mention-some worth 1, mismatching 0, exhaustive `1 − δ` (cost). -/
def dp (ε δ : ℚ) : DecisionProblem ℚ Goal Response where
  utility
    | .g₁, .ms1 => 1
    | .g₁, .ms2 => 0
    | .g₂, .ms1 => 0
    | .g₂, .ms2 => 1
    | _, .exh => 1 - δ
  prior
    | .g₁ => 1 - ε
    | .g₂ => ε

private theorem sum_goal (f : Goal → ℚ) : (∑ g : Goal, f g) = f .g₁ + f .g₂ := by
  rw [show (Finset.univ : Finset Goal) = {.g₁, .g₂} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]

theorem eu_ms1 (ε δ : ℚ) : expectedUtility (dp ε δ) .ms1 = 1 - ε := by
  simp only [expectedUtility, sum_goal, dp]; ring

theorem eu_ms2 (ε δ : ℚ) : expectedUtility (dp ε δ) .ms2 = ε := by
  simp only [expectedUtility, sum_goal, dp]; ring

theorem eu_exh (ε δ : ℚ) : expectedUtility (dp ε δ) .exh = 1 - δ := by
  simp only [expectedUtility, sum_goal, dp]; ring

/-! ### The behavioral policy π = SoftMax(α · EU)

The paper's π softmaxes the goal-*marginal* expected utility — the agent
acts under its own uncertainty. Instantiated as the canonical softmax
speaker over the `(ε, δ)`-indexed state space. -/

/-- Score for the canonical speaker: `α · EU(r)` at condition `(ε, δ)`. -/
noncomputable def policyScore (α : ℝ) (p : ℚ × ℚ) (r : Response) : EReal :=
  ((α * ((expectedUtility (dp p.1 p.2) r : ℚ) : ℝ) : ℝ) : EReal)

instance (α : ℝ) : RSA.Canonical.ViableSpeaker (policyScore α) where
  no_top _ _ := EReal.coe_ne_top _
  some_finite _ := ⟨.exh, EReal.coe_ne_bot _⟩

/-- The paper's behavioral policy `π(r) = SoftMax(α · EU(r))`. -/
noncomputable def policy (α : ℝ) (ε δ : ℚ) : PMF Response :=
  RSA.Canonical.S1 (policyScore α) (ε, δ)

private theorem policy_lt_policy {α : ℝ} (hα : 0 < α) {ε δ : ℚ} {r₁ r₂ : Response}
    (h : expectedUtility (dp ε δ) r₁ < expectedUtility (dp ε δ) r₂) :
    policy α ε δ r₁ < policy α ε δ r₂ := by
  rw [policy, RSA.Canonical.S1_prefers_iff]
  exact EReal.coe_lt_coe (mul_lt_mul_of_pos_left (by exact_mod_cast h) hα)

/-- **The uncertainty flip**: once uncertainty exceeds the exhaustive cost
(`δ < ε ≤ 1/2`), the safe exhaustive answer beats both targeted answers —
the paper's "act safe under uncertainty" effect (fitted:
δ_L = 0.32 < ε_H = 0.49). -/
theorem policy_prefers_exh_of_uncertain {α : ℝ} (hα : 0 < α) {ε δ : ℚ}
    (h₁ : δ < ε) (h₂ : ε ≤ 1/2) :
    policy α ε δ .ms1 < policy α ε δ .exh ∧ policy α ε δ .ms2 < policy α ε δ .exh :=
  ⟨policy_lt_policy hα (by rw [eu_ms1, eu_exh]; linarith),
   policy_lt_policy hα (by rw [eu_ms2, eu_exh]; linarith)⟩

/-- Under low uncertainty (`ε < δ`, `ε < 1/2`) the matching mention-some
wins (fitted: ε_L = 0.17 < δ_L = 0.32). -/
theorem policy_prefers_ms1_of_confident {α : ℝ} (hα : 0 < α) {ε δ : ℚ}
    (h₁ : ε < δ) (h₂ : ε < 1/2) :
    policy α ε δ .exh < policy α ε δ .ms1 ∧ policy α ε δ .ms2 < policy α ε δ .ms1 :=
  ⟨policy_lt_policy hα (by rw [eu_exh, eu_ms1]; linarith),
   policy_lt_policy hα (by rw [eu_ms2, eu_ms1]; linarith)⟩

/-! ### Expected regret of the best action: EVPI = min ε δ -/

private theorem bestUtilityAt_eq_one {ε δ : ℚ} (hδ0 : 0 ≤ δ) (g : Goal) :
    bestUtilityAt (dp ε δ) Finset.univ g = 1 := by
  rw [bestUtilityAt, dif_pos Finset.univ_nonempty]
  refine le_antisymm (Finset.sup'_le _ _ fun r _ => ?_) ?_
  · cases g <;> cases r <;> simp [dp] <;> linarith
  · cases g
    · exact Finset.le_sup' (α := ℚ) ((dp ε δ).utility .g₁) (Finset.mem_univ .ms1)
    · exact Finset.le_sup' (α := ℚ) ((dp ε δ).utility .g₂) (Finset.mem_univ .ms2)

private theorem oracleValue_eq_one {ε δ : ℚ} (hδ0 : 0 ≤ δ) :
    oracleValue (dp ε δ) Finset.univ = 1 := by
  rw [oracleValue, sum_goal, bestUtilityAt_eq_one hδ0, bestUtilityAt_eq_one hδ0]
  show (1 - ε) * 1 + ε * 1 = 1
  ring

private theorem dpValue_eq {ε δ : ℚ} (hε : ε ≤ 1/2) :
    DecisionProblem.value (dp ε δ) Finset.univ = 1 - min ε δ := by
  rw [DecisionProblem.value, dif_pos Finset.univ_nonempty]
  refine le_antisymm (Finset.sup'_le _ _ fun r _ => ?_) ?_
  · have h₁ := min_le_left ε δ
    have h₂ := min_le_right ε δ
    cases r
    · rw [eu_ms1]; linarith
    · rw [eu_ms2]; linarith
    · rw [eu_exh]; linarith
  · rcases min_cases ε δ with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · calc 1 - min ε δ = expectedUtility (dp ε δ) Response.ms1 := by rw [eu_ms1, hmin]
        _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ Response.ms1)
    · calc 1 - min ε δ = expectedUtility (dp ε δ) Response.exh := by rw [eu_exh, hmin]
        _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ Response.exh)

/-- **The interaction in closed form**: for the paper's decision problem,
the expected regret of the best action — `ExpRegret(r*)`, i.e. the expected
value of perfect information ([raiffa-schlaifer-1961], `evpi`) — is
`min ε δ`. Regret is bounded by the
uncertainty *and* by the cost of the safe action, so uncertainty raises
regret only while it stays below the cost: the paper's headline claim that
uncertainty matters most when acting incorrectly is costly. -/
theorem evpi_eq_min {ε δ : ℚ} (hε : ε ≤ 1/2) (hδ0 : 0 ≤ δ) :
    evpi (dp ε δ) Finset.univ = min ε δ := by
  rw [evpi, oracleValue_eq_one hδ0, dpValue_eq hε]
  ring

/-! ### The CQ gate `P(r_cq) = Logistic(τ · (ExpRegret(r*) − c))` -/

/-- The logistic CQ gate over the regret signal `x`. -/
noncomputable def cqGate (τ c x : ℝ) : ℝ :=
  (1 + Real.exp (-(τ * (x - c))))⁻¹

theorem cqGate_pos (τ c x : ℝ) : 0 < cqGate τ c x := by
  rw [cqGate]
  positivity

theorem cqGate_le_one (τ c x : ℝ) : cqGate τ c x ≤ 1 := by
  rw [cqGate]
  rw [inv_le_one_iff₀]
  right
  linarith [Real.exp_pos (-(τ * (x - c)))]

/-- The gate is strictly increasing in expected regret (for `τ > 0`):
more to lose from acting → more clarification. -/
theorem cqGate_strictMono {τ : ℝ} (hτ : 0 < τ) (c : ℝ) : StrictMono (cqGate τ c) := by
  intro x y hxy
  rw [cqGate, cqGate]
  have hexp : Real.exp (-(τ * (y - c))) < Real.exp (-(τ * (x - c))) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr (by linarith)

/-- The paper's CQ probability at condition `(ε, δ)`: the logistic gate
applied to the expected regret of the best action. -/
noncomputable def cqProb (τ c : ℝ) (ε δ : ℚ) : ℝ :=
  cqGate τ c ((evpi (dp ε δ) Finset.univ : ℚ) : ℝ)

/-! ### Gate-level Experiment 1 predictions

Fitted condition parameters (Bayesian posterior means): ε_L = 0.17,
ε_H = 0.49 (low/high uncertainty), δ_S = 0.11, δ_L = 0.32 (small/large
option space). The predictions hold for every `τ > 0` and threshold `c`;
only the orderings `δ_S < ε_L < δ_L` and `ε_L < ε_H ≤ 1/2` matter. -/

def epsLow : ℚ := 17/100
def epsHigh : ℚ := 49/100
def deltaSmall : ℚ := 11/100
def deltaLarge : ℚ := 32/100

/-- **TL;JustAsk** (prediction 1): with a large option space, more
clarification under high uncertainty. -/
theorem tl_justAsk {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    cqProb τ c epsLow deltaLarge < cqProb τ c epsHigh deltaLarge := by
  rw [cqProb, cqProb,
      evpi_eq_min (by norm_num [epsLow]) (by norm_num [deltaLarge]),
      evpi_eq_min (by norm_num [epsHigh]) (by norm_num [deltaLarge]),
      show min epsLow deltaLarge = 17/100 from by norm_num [min_def, epsLow, deltaLarge],
      show min epsHigh deltaLarge = 32/100 from by norm_num [min_def, epsHigh, deltaLarge]]
  exact cqGate_strictMono hτ c (by norm_num)

/-- **NoNeedToAsk** (prediction 2): with a small option space, *no*
difference in clarification between high and low uncertainty — an exact
equality: the regret signal is capped at `δ_S` in both conditions. -/
theorem noNeedToAsk (τ c : ℝ) :
    cqProb τ c epsLow deltaSmall = cqProb τ c epsHigh deltaSmall := by
  rw [cqProb, cqProb,
      evpi_eq_min (by norm_num [epsLow]) (by norm_num [deltaSmall]),
      evpi_eq_min (by norm_num [epsHigh]) (by norm_num [deltaSmall]),
      show min epsLow deltaSmall = 11/100 from by norm_num [min_def, epsLow, deltaSmall],
      show min epsHigh deltaSmall = 11/100 from by norm_num [min_def, epsHigh, deltaSmall]]

/-- **WorthAsking** (the cost effect; Exp 2's prediction 7 at the model
level): clarification is more likely when the safe action is costlier, at
either uncertainty level. The model is fitted to Exp 1, where δ is its only
cost knob. -/
theorem worthAsking {τ : ℝ} (hτ : 0 < τ) (c : ℝ) {ε : ℚ} (hε : ε ≤ 1/2)
    (h : deltaSmall < ε) :
    cqProb τ c ε deltaSmall < cqProb τ c ε deltaLarge := by
  rw [cqProb, cqProb, evpi_eq_min hε (by norm_num [deltaSmall]),
      evpi_eq_min hε (by norm_num [deltaLarge]),
      show min ε deltaSmall = deltaSmall from min_eq_right h.le]
  refine cqGate_strictMono hτ c ?_
  exact_mod_cast lt_min h (by norm_num [deltaSmall, deltaLarge])

/-- **The interaction** (the paper's headline): uncertainty raises
clarification when the safe action is costly (large option space) and has
*no* effect when it is cheap (small option space). -/
theorem uncertainty_matters_most_when_costly {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    cqProb τ c epsLow deltaSmall = cqProb τ c epsHigh deltaSmall ∧
    cqProb τ c epsLow deltaLarge < cqProb τ c epsHigh deltaLarge :=
  ⟨noNeedToAsk τ c, tl_justAsk hτ c⟩

/-! ### The shared decision-rule instance: a soft gate

The logistic gate instantiates `DongEtAl2026.ClarifyRule` as a *soft*
threshold, against [dong-etal-2026]'s sharp `DongEtAl2026.sharpRule`: it
is never binary — at zero net value it clarifies with probability 1/2
(`softGateRule_apply_zero`, vs `DongEtAl2026.sharpRule_binary`). Cf. the
paper's Exp 2 contrast between binarized CQ rates and gradient action
rates. -/

/-- The logistic gate as a `ClarifyRule` over the net regret signal. -/
noncomputable def softGateRule {τ : ℝ} (hτ : 0 < τ) :
    DongEtAl2026.ClarifyRule where
  propensity := cqGate τ 0
  mono := (cqGate_strictMono hτ 0).monotone
  nonneg x := (cqGate_pos τ 0 x).le
  le_one x := cqGate_le_one τ 0 x

/-- `cqProb` is the soft rule applied to the net signal `ExpRegret − c`. -/
theorem cqProb_eq_softGateRule {τ : ℝ} (hτ : 0 < τ) (c : ℝ) (ε δ : ℚ) :
    cqProb τ c ε δ
      = (softGateRule hτ).propensity (((evpi (dp ε δ) Finset.univ : ℚ) : ℝ) - c) := by
  show cqGate τ c _ = cqGate τ 0 _
  rw [cqGate, cqGate]
  norm_num

/-- Unlike the sharp rule, the soft gate is never binary: at zero net value
it clarifies with probability 1/2. -/
theorem softGateRule_apply_zero {τ : ℝ} (hτ : 0 < τ) :
    (softGateRule hτ).propensity 0 = 1/2 := by
  show cqGate τ 0 0 = 1/2
  rw [cqGate]
  norm_num [Real.exp_zero]

/-! ### The layered reaction policy -/

/-- A reaction: clarify, or commit to a direct response. -/
inductive Reaction where
  | cq
  | act (r : Response)
  deriving DecidableEq, Repr

/-- The paper's layered mixture: clarify with probability `q`, otherwise
act according to the behavioral policy. -/
noncomputable def layered (q : ℝ≥0) (hq : q ≤ 1) (pol : PMF Response) : PMF Reaction :=
  (PMF.bernoulliMix q hq).bind fun ask => if ask then PMF.pure .cq else pol.map .act

theorem layered_apply_cq (q : ℝ≥0) (hq : q ≤ 1) (pol : PMF Response) :
    layered q hq pol .cq = q := by
  rw [layered, PMF.bind_apply, tsum_bool]
  simp [PMF.bernoulliMix_apply, PMF.map_apply,
    show ∀ r : Response, Reaction.cq ≠ .act r from fun r => by simp]

theorem layered_apply_act (q : ℝ≥0) (hq : q ≤ 1) (pol : PMF Response) (r : Response) :
    layered q hq pol (.act r) = (1 - (q : ℝ≥0∞)) * pol r := by
  rw [layered, PMF.bind_apply, tsum_bool]
  have hmap : pol.map Reaction.act (.act r) = pol r := by
    rw [PMF.map_apply]
    simp only [Reaction.act.injEq]
    exact (tsum_eq_single r fun r' hne => if_neg fun h => hne h.symm).trans (if_pos rfl)
  simp [PMF.bernoulliMix_apply, hmap]

/-- The full reaction policy at condition `(ε, δ)`: gate by the logistic of
the expected regret, then act by the softmax policy. -/
noncomputable def reaction (τ c α : ℝ) (ε δ : ℚ) : PMF Reaction :=
  layered (Real.toNNReal (cqProb τ c ε δ))
    (by
      rw [← Real.toNNReal_one]
      exact Real.toNNReal_mono (cqGate_le_one _ _ _))
    (policy α ε δ)

/-! ### RSA reinterpretation: the post-clarification speaker and a listener

Everything below is this file's **extension**, not the paper's model. The
goal-*conditioned* speaker — softmax of `U(g, ·)` with inapplicable
responses gated to `⊥` — is the ε → 0 / post-clarification limit of `π`,
and coincides with [hawkins-etal-2025]'s action-utility respondent R₁ at
β = 1, w_c = 0 (their `responseTruth` gate). Inverting it with a Bayesian
listener connects the model to the canonical RSA pipeline; the paper itself
has no listener. -/

/-- Does response `r` address goal `g`? ([hawkins-etal-2025]'s `responseTruth`.) -/
def respApplies : Response → Goal → Bool
  | .ms1, .g₁ => true
  | .ms2, .g₂ => true
  | .exh, _   => true
  | _,    _   => false

/-- Action value `U(g, r)` as a real: 1 for matching mention-some,
`exhVal = 1 − δ` for exhaustive, 0 for a mismatch. -/
def actVal (exhVal : ℝ) : Response → Goal → ℝ
  | .ms1, .g₁ => 1
  | .ms2, .g₂ => 1
  | .exh, _   => exhVal
  | _,    _   => 0

/-- Goal-conditioned speaker utility: `α · U(g, r)` on applicable
responses, `⊥` (softmax weight 0) otherwise. -/
noncomputable def util (exhVal α : ℝ) : Goal → Response → EReal :=
  fun g r => if respApplies r g then ((α * actVal exhVal r g : ℝ) : EReal) else (⊥ : EReal)

instance instViable (exhVal α : ℝ) : RSA.Canonical.ViableSpeaker (util exhVal α) where
  no_top g r := by
    unfold util
    split
    · exact EReal.coe_ne_top _
    · exact bot_ne_top
  some_finite g := ⟨.exh, by
    unfold util
    rw [if_pos (show respApplies .exh g = true by cases g <;> rfl)]
    exact EReal.coe_ne_bot _⟩

/-- The goal-conditioned (post-clarification) speaker. -/
noncomputable def speaker (exhVal α : ℝ) : Goal → PMF Response :=
  RSA.Canonical.S1 (util exhVal α)

private theorem util_applies {exhVal α : ℝ} {r : Response} {g : Goal}
    (h : respApplies r g = true) :
    util exhVal α g r = ((α * actVal exhVal r g : ℝ) : EReal) := by
  unfold util; rw [if_pos h]

private theorem util_inapplies {exhVal α : ℝ} {r : Response} {g : Goal}
    (h : respApplies r g = false) : util exhVal α g r = ⊥ := by
  unfold util; rw [if_neg (by simp [h])]

private theorem speaker_ne_zero {exhVal α : ℝ} {g : Goal} {r : Response}
    (h : respApplies r g = true) : speaker exhVal α g r ≠ 0 :=
  RSA.Canonical.S1_ne_zero (util exhVal α)
    (by rw [util_applies h]; exact EReal.coe_ne_bot _)

private theorem speaker_eq_zero {exhVal α : ℝ} {g : Goal} {r : Response}
    (h : respApplies r g = false) : speaker exhVal α g r = 0 := by
  have hbot : util exhVal α g r = ⊥ := util_inapplies h
  unfold speaker RSA.Canonical.S1
  rw [PMF.apply_eq_zero_iff, PMF.support_softmax]
  simp [hbot]

/-- Knowing the goal, the speaker prefers the targeted answer over the
exhaustive one whenever the exhaustive answer carries any cost
(`exhVal < 1`), for any α > 0. -/
theorem S1_g1_prefers_ms1 {exhVal α : ℝ} (hα : 0 < α) (hv : exhVal < 1) :
    speaker exhVal α .g₁ .exh < speaker exhVal α .g₁ .ms1 := by
  rw [speaker, RSA.Canonical.S1_prefers_iff,
      util_applies (show respApplies .exh .g₁ = true from rfl),
      util_applies (show respApplies .ms1 .g₁ = true from rfl)]
  exact EReal.coe_lt_coe (by simp only [actVal]; nlinarith)

/-- The speaker never produces a mismatching answer: its utility is `⊥`. -/
theorem S1_g1_avoids_ms2 (exhVal α : ℝ) :
    speaker exhVal α .g₁ .ms2 < speaker exhVal α .g₁ .ms1 := by
  rw [speaker, RSA.Canonical.S1_prefers_iff,
      util_inapplies (show respApplies .ms2 .g₁ = false by decide),
      util_applies (show respApplies .ms1 .g₁ = true from rfl)]
  exact EReal.bot_lt_coe _

/-! The cross-condition δ-sensitivity of the exhaustive answer
(`S1(exh | g₁, δ_S) > S1(exh | g₁, δ_L)`: exhaustive answers are more
viable when the option space is small) is Exp 1's option-space cost effect
(predictions 3–4; the credible negative effect of space size on exhaustive
rates). It is a cross-model comparison outside the single-distribution
`S1_prefers_iff` vocabulary; at the policy level the same effect is `eu_exh`
monotone in δ. -/

/-- The questioner's prior over goals, `(1 − ε) : ε`, normalised. -/
noncomputable def priorWeight (pg1 pg2 : ℝ) : Goal → ℝ≥0∞
  | .g₁ => ENNReal.ofReal pg1
  | .g₂ => ENNReal.ofReal pg2

private theorem priorWeight_tsum (pg1 pg2 : ℝ) :
    (∑' g, priorWeight pg1 pg2 g) = ENNReal.ofReal pg1 + ENNReal.ofReal pg2 := by
  rw [tsum_fintype, show (Finset.univ : Finset Goal) = {Goal.g₁, Goal.g₂} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rfl

/-- The world prior, normalised to a PMF. -/
noncomputable def worldPrior (pg1 pg2 : ℝ) (h1 : 0 < pg1) (_h2 : 0 < pg2) : PMF Goal :=
  PMF.normalize (priorWeight pg1 pg2)
    (by rw [priorWeight_tsum]
        exact ((ENNReal.ofReal_pos.mpr h1).trans_le le_self_add).ne')
    (by rw [priorWeight_tsum]
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)

private theorem worldPrior_ne_zero {pg1 pg2 : ℝ} (h1 : 0 < pg1) (h2 : 0 < pg2) (g : Goal) :
    worldPrior pg1 pg2 h1 h2 g ≠ 0 := by
  rw [worldPrior, PMF.normalize_apply]
  refine mul_ne_zero ?_ (ENNReal.inv_ne_zero.mpr ?_)
  · cases g
    · exact (ENNReal.ofReal_pos.mpr h1).ne'
    · exact (ENNReal.ofReal_pos.mpr h2).ne'
  · rw [priorWeight_tsum]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩

/-- The questioner as Bayesian listener (this file's extension): the
posterior over goals given the response. -/
noncomputable def listener (exhVal pg1 pg2 α : ℝ) (h1 : 0 < pg1) (h2 : 0 < pg2)
    (r : Response)
    (h : PMF.marginal (speaker exhVal α) (worldPrior pg1 pg2 h1 h2) r ≠ 0) :
    PMF Goal :=
  PMF.posterior (speaker exhVal α) (worldPrior pg1 pg2 h1 h2) r h

private theorem marginal_ne_zero_at {exhVal pg1 pg2 α : ℝ} (h1 : 0 < pg1) (h2 : 0 < pg2)
    (g : Goal) {r : Response} (hr : respApplies r g = true) :
    PMF.marginal (speaker exhVal α) (worldPrior pg1 pg2 h1 h2) r ≠ 0 :=
  PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero h1 h2 g) (speaker_ne_zero hr)

/-- The listener hearing ms1 infers g₁ with certainty (ms1 is never
produced for g₂). Prior 83 : 17 = (1 − ε_L) : ε_L. -/
theorem L1_ms1_infers_g1 :
    listener (68/100) 83 17 1 (by norm_num) (by norm_num) .ms1
        (marginal_ne_zero_at (by norm_num) (by norm_num) .g₁ rfl) .g₂
      < listener (68/100) 83 17 1 (by norm_num) (by norm_num) .ms1
        (marginal_ne_zero_at (by norm_num) (by norm_num) .g₁ rfl) .g₁ := by
  rw [listener, PMF.posterior_lt_iff_score_lt,
      speaker_eq_zero (show respApplies .ms1 .g₂ = false by decide), mul_zero]
  exact pos_iff_ne_zero.mpr
    (mul_ne_zero (worldPrior_ne_zero (by norm_num) (by norm_num) .g₁)
      (speaker_ne_zero rfl))

/-- Targeted responses stay fully informative even at high uncertainty
(prior 51 : 49 = (1 − ε_H) : ε_H). -/
theorem L1_high_ms1_still_certain :
    listener (68/100) 51 49 1 (by norm_num) (by norm_num) .ms1
        (marginal_ne_zero_at (by norm_num) (by norm_num) .g₁ rfl) .g₂
      < listener (68/100) 51 49 1 (by norm_num) (by norm_num) .ms1
        (marginal_ne_zero_at (by norm_num) (by norm_num) .g₁ rfl) .g₁ := by
  rw [listener, PMF.posterior_lt_iff_score_lt,
      speaker_eq_zero (show respApplies .ms1 .g₂ = false by decide), mul_zero]
  exact pos_iff_ne_zero.mpr
    (mul_ne_zero (worldPrior_ne_zero (by norm_num) (by norm_num) .g₁)
      (speaker_ne_zero rfl))

/-- The speaker's exhaustive-answer probability is goal-symmetric: the
utility multisets at g₁ and g₂ coincide under the ms1 ↔ ms2 swap. -/
private theorem speaker_exh_symm (exhVal α : ℝ) :
    speaker exhVal α .g₁ .exh = speaker exhVal α .g₂ .exh := by
  unfold speaker RSA.Canonical.S1
  rw [PMF.softmax_apply, PMF.softmax_apply]
  congr 1
  rw [show (Finset.univ : Finset Response) = {.ms1, .ms2, .exh} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      PMF.softmaxWeight_apply, PMF.softmaxWeight_apply, PMF.softmaxWeight_apply,
      PMF.softmaxWeight_apply, PMF.softmaxWeight_apply, PMF.softmaxWeight_apply,
      util_applies (show respApplies .ms1 .g₁ = true from rfl),
      util_inapplies (show respApplies .ms2 .g₁ = false by decide),
      util_applies (show respApplies .exh .g₁ = true from rfl),
      util_inapplies (show respApplies .ms1 .g₂ = false by decide),
      util_applies (show respApplies .ms2 .g₂ = true from rfl),
      util_applies (show respApplies .exh .g₂ = true from rfl)]
  show EReal.exp _ + (EReal.exp ⊥ + EReal.exp _)
    = EReal.exp ⊥ + (EReal.exp _ + EReal.exp _)
  have hms : actVal exhVal .ms1 .g₁ = actVal exhVal .ms2 .g₂ := rfl
  have hexh : actVal exhVal .exh .g₁ = actVal exhVal .exh .g₂ := rfl
  rw [hms, hexh]
  ring

/-- The exhaustive answer transmits the prior: `S1(exh | ·)` is
goal-symmetric, so the listener's posterior given exh is the prior,
83 : 17. -/
theorem L1_exh_transmits_prior :
    listener (68/100) 83 17 1 (by norm_num) (by norm_num) .exh
        (marginal_ne_zero_at (by norm_num) (by norm_num) .g₁ (by decide)) .g₂
      < listener (68/100) 83 17 1 (by norm_num) (by norm_num) .exh
        (marginal_ne_zero_at (by norm_num) (by norm_num) .g₁ (by decide)) .g₁ := by
  rw [listener, PMF.posterior_lt_iff_score_lt, ← speaker_exh_symm]
  rw [mul_comm (worldPrior 83 17 _ _ .g₂), mul_comm (worldPrior 83 17 _ _ .g₁)]
  refine (ENNReal.mul_lt_mul_iff_right
    (speaker_ne_zero (show respApplies .exh .g₁ = true from rfl))
    (PMF.apply_ne_top _ _)).mpr ?_
  rw [worldPrior, PMF.normalize_apply, PMF.normalize_apply]
  refine (ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr (by
      rw [priorWeight_tsum]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
    (ENNReal.inv_ne_top.mpr (by
      rw [priorWeight_tsum]
      exact ((ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ) < 83)).trans_le
        le_self_add).ne'))).mpr ?_
  show ENNReal.ofReal 17 < ENNReal.ofReal 83
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

end TsvilodubEtAl2026
