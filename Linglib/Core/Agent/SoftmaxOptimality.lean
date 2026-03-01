import Linglib.Core.Agent.RationalAction
import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits
import Mathlib.Data.Rat.Cast.Defs

/-!
# Softmax Optimality: The Decision-Theoretic Foundation of Soft-Rational Agents

The deepest claim in the RSA architecture is that the softmax agent IS the
entropy-regularized expected-utility maximizer. This file makes that connection
explicit by bridging `DecisionProblem` (ℚ) from `DecisionTheory.lean` with
`RationalAction` (ℝ) from `RationalAction.lean`.

## Results

1. **Construction** (§1): A `DecisionProblem` yields a `RationalAction` via
   softmax over expected utility, bridging the ℚ/ℝ gap.

2. **Monotonicity** (§2): Higher EU ⟹ higher choice probability (α > 0).

3. **Entropy-regularized optimality** (§3): The softmax agent uniquely maximizes
   `∑ p(a)·EU(a) + (1/α)·H(p)` — the Gibbs Variational Principle in
   decision-theoretic language.

4. **Hard-max convergence** (§4): As α → ∞, the softmax agent converges to
   the EU-optimal deterministic policy.

5. **Round-trip** (§5): Extracting utility from a softmax agent and
   reconstructing recovers the same policy.
-/

namespace Core

open Real BigOperators Finset Filter Topology

-- ============================================================================
-- §1. Expected Utility in ℝ and the Softmax Agent Constructor
-- ============================================================================

/-- Expected utility cast to ℝ for interfacing with softmax/RationalAction. -/
noncomputable def expectedUtilityR {W A : Type*} [Fintype W]
    (dp : DecisionTheory.DecisionProblem W A) (a : A) : ℝ :=
  ∑ w : W, (dp.prior w : ℝ) * (dp.utility w a : ℝ)

/-- EU in ℝ is non-negative when utility and prior are non-negative. -/
theorem expectedUtilityR_nonneg {W A : Type*} [Fintype W]
    (dp : DecisionTheory.DecisionProblem W A) (a : A)
    (hpr : ∀ w, 0 ≤ dp.prior w) (hu : ∀ w, 0 ≤ dp.utility w a) :
    0 ≤ expectedUtilityR dp a :=
  Finset.sum_nonneg fun w _ =>
    mul_nonneg (Rat.cast_nonneg.mpr (hpr w)) (Rat.cast_nonneg.mpr (hu w))

/-- ℚ-ordering of EU is preserved under the cast to ℝ. -/
theorem expectedUtilityR_mono {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionTheory.DecisionProblem W A) (a₁ a₂ : A)
    (h : DecisionTheory.expectedUtility dp a₁ ≤ DecisionTheory.expectedUtility dp a₂) :
    expectedUtilityR dp a₁ ≤ expectedUtilityR dp a₂ := by
  simp only [expectedUtilityR, DecisionTheory.expectedUtility] at *
  exact_mod_cast h

/-- Softmax agent from a decision problem: score(a) = exp(α · EU(a)).

The state type is `Unit` because the decision problem's prior already
encodes the agent's beliefs — there is no external state to condition on. -/
noncomputable def RationalAction.fromDecisionProblem {W A : Type*}
    [Fintype W] [Fintype A]
    (dp : DecisionTheory.DecisionProblem W A) (α : ℝ) : RationalAction Unit A :=
  RationalAction.fromSoftmax (fun () a => expectedUtilityR dp a) α

-- ============================================================================
-- §2. EU Ordering ↔ Policy Ordering
-- ============================================================================

/-- Higher EU implies higher choice probability (α > 0). -/
theorem fromDP_policy_mono {W A : Type*} [Fintype W] [Fintype A] [Nonempty A]
    (dp : DecisionTheory.DecisionProblem W A) {α : ℝ} (hα : 0 < α)
    (a₁ a₂ : A) (h : expectedUtilityR dp a₁ ≤ expectedUtilityR dp a₂) :
    (RationalAction.fromDecisionProblem dp α).policy () a₁ ≤
    (RationalAction.fromDecisionProblem dp α).policy () a₂ := by
  simp only [RationalAction.fromDecisionProblem,
             RationalAction.fromSoftmax_policy_eq]
  exact softmax_mono _ hα a₁ a₂ h

/-- Strict version: strictly higher EU implies strictly higher probability. -/
theorem fromDP_policy_strict_mono {W A : Type*} [Fintype W] [Fintype A] [Nonempty A]
    (dp : DecisionTheory.DecisionProblem W A) {α : ℝ} (hα : 0 < α)
    (a₁ a₂ : A) (h : expectedUtilityR dp a₁ < expectedUtilityR dp a₂) :
    (RationalAction.fromDecisionProblem dp α).policy () a₁ <
    (RationalAction.fromDecisionProblem dp α).policy () a₂ := by
  simp only [RationalAction.fromDecisionProblem,
             RationalAction.fromSoftmax_policy_eq]
  exact softmax_strict_mono _ hα a₁ a₂ h

-- ============================================================================
-- §3. Entropy-Regularized EU Maximality
-- ============================================================================

/-- The softmax agent uniquely maximizes entropy-regularized expected utility:
    p* = argmax_p [∑ p(a)·EU(a) + (1/α)·H(p)].

This is the decision-theoretic content of the Gibbs Variational Principle.
The objective `entropyRegObjective` from `RationalAction.lean` is exactly
`∑ p(a)·s(a) + (1/α)·H(p)` — we just instantiate `s = EU`. -/
theorem softmax_maximizes_EU_plus_entropy {W A : Type*}
    [Fintype W] [Fintype A] [Nonempty A]
    (dp : DecisionTheory.DecisionProblem W A) {α : ℝ} (hα : 0 < α)
    (p : A → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    entropyRegObjective (fun a => expectedUtilityR dp a) α p ≤
    entropyRegObjective (fun a => expectedUtilityR dp a) α
      ((RationalAction.fromDecisionProblem dp α).policy () ·) := by
  -- The policy of fromDecisionProblem equals softmax over EU
  have hpol : ∀ a, (RationalAction.fromDecisionProblem dp α).policy () a =
      softmax (fun a => expectedUtilityR dp a) α a := by
    intro a
    exact RationalAction.fromSoftmax_policy_eq _ α () a
  simp_rw [show (fun a => (RationalAction.fromDecisionProblem dp α).policy () a) =
    softmax (fun a => expectedUtilityR dp a) α from funext hpol]
  exact softmax_maximizes_entropyReg _ α hα p hp_nn hp_sum

/-- The softmax agent is the UNIQUE maximizer: any distribution achieving
the same objective value must equal the softmax policy. -/
theorem softmax_unique_EU_maximizer {W A : Type*}
    [Fintype W] [Fintype A] [Nonempty A]
    (dp : DecisionTheory.DecisionProblem W A) {α : ℝ} (hα : 0 < α)
    (p : A → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (h_max : entropyRegObjective (fun a => expectedUtilityR dp a) α p =
             entropyRegObjective (fun a => expectedUtilityR dp a) α
               (softmax (fun a => expectedUtilityR dp a) α)) :
    p = softmax (fun a => expectedUtilityR dp a) α :=
  softmax_unique_maximizer _ α hα p hp_nn hp_sum h_max

-- ============================================================================
-- §4. Hard-Max Convergence
-- ============================================================================

/-- As α → ∞, the softmax agent converges to the EU-optimal deterministic
policy: the probability of the unique EU-maximizing action → 1.

This is the decision-theoretic content of `tendsto_softmax_infty_at_max`
from `Softmax.Limits`. -/
theorem fromDP_converges_to_optimal {W A : Type*}
    [Fintype W] [Fintype A] [Nonempty A] [DecidableEq A]
    (dp : DecisionTheory.DecisionProblem W A) (a_opt : A)
    (h_opt : ∀ a, a ≠ a_opt → expectedUtilityR dp a < expectedUtilityR dp a_opt) :
    Tendsto (fun α => (RationalAction.fromDecisionProblem dp α).policy () a_opt)
      atTop (𝓝 1) := by
  have hpol : ∀ α, (RationalAction.fromDecisionProblem dp α).policy () a_opt =
      softmax (fun a => expectedUtilityR dp a) α a_opt :=
    fun α => RationalAction.fromSoftmax_policy_eq _ α () a_opt
  simp_rw [hpol]
  exact Softmax.tendsto_softmax_infty_at_max _ a_opt h_opt

/-- As α → ∞, any non-optimal action gets probability → 0. -/
theorem fromDP_nonoptimal_vanishes {W A : Type*}
    [Fintype W] [Fintype A] [Nonempty A] [DecidableEq A]
    (dp : DecisionTheory.DecisionProblem W A) (a_opt a : A)
    (h_opt : ∀ a', a' ≠ a_opt → expectedUtilityR dp a' < expectedUtilityR dp a_opt)
    (ha : a ≠ a_opt) :
    Tendsto (fun α => (RationalAction.fromDecisionProblem dp α).policy () a)
      atTop (𝓝 0) := by
  have hpol : ∀ α', (RationalAction.fromDecisionProblem dp α').policy () a =
      softmax (fun a => expectedUtilityR dp a) α' a :=
    fun α' => RationalAction.fromSoftmax_policy_eq _ α' () a
  simp_rw [hpol]
  have hlim := Softmax.tendsto_softmax_infty_unique_max _ a_opt h_opt a
  simp only [if_neg ha] at hlim
  exact hlim

-- ============================================================================
-- §5. Extracting a Decision Problem from a RationalAction
-- ============================================================================

/-- Extract the implicit utility function from a softmax-parameterized agent.

If `ra = fromSoftmax u α`, then `toUtility ra α a = u a + const` (up to
the translation invariance of softmax). -/
noncomputable def RationalAction.toUtility {A : Type*} [Fintype A]
    (ra : RationalAction Unit A)
    (α : ℝ) (a : A) (_ha : 0 < ra.score () a) : ℝ :=
  Real.log (ra.score () a) / α

/-- Round-trip: constructing via fromSoftmax and extracting utility recovers
the original utility (the log inverts the exp, and dividing by α cancels). -/
theorem fromSoftmax_toUtility_eq {A : Type*} [Fintype A]
    (utility : Unit → A → ℝ) (α : ℝ) (hα : α ≠ 0) (a : A) :
    (RationalAction.fromSoftmax utility α).toUtility α a
      (by exact exp_pos _) =
    utility () a := by
  simp only [RationalAction.toUtility, RationalAction.fromSoftmax,
             Real.log_exp, mul_div_cancel_left₀ _ hα]

/-- Round-trip for the full agent: fromSoftmax ∘ toUtility recovers the same
policy (the softmax is translation-invariant so the constant cancels). -/
theorem fromSoftmax_roundtrip_policy {A : Type*} [Fintype A] [Nonempty A]
    (utility : Unit → A → ℝ) (α : ℝ) (hα : α ≠ 0) (a : A) :
    (RationalAction.fromSoftmax utility α).policy () a =
    (RationalAction.fromSoftmax
      (fun _ a' => (RationalAction.fromSoftmax utility α).toUtility α a'
        (by exact exp_pos _)) α).policy () a := by
  simp only [RationalAction.toUtility,
             RationalAction.fromSoftmax, Real.log_exp, mul_div_cancel_left₀ _ hα]

end Core
