import Linglib.Core.Agent.DecisionTheory
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Clarification: When to Ask vs. When to Act
[raiffa-schlaifer-1961]

When agents face uncertainty about an interlocutor's goals, they choose
between acting under uncertainty and asking clarification questions (CQs).
Both [tsvilodub-etal-2026] and [dong-etal-2026] find that this
choice is governed by the **expected value of perfect information** (EVPI):
agents clarify when EVPI exceeds communication cost.

EVPI captures the interaction of uncertainty and stakes — it is high when
(a) uncertainty is high AND (b) acting incorrectly is costly. This
interaction is the core empirical finding shared by both papers.

## Connection to existing infrastructure

EVPI is the maximum possible `questionUtility` ([van-rooy-2003]):
it equals `questionUtility` on the identity partition, where each world
is its own cell. Any specific clarification question yields at most EVPI.

## The shared decision-rule contract

Both accounts decide clarification from the same net value-of-information
signal but through different rules: [dong-etal-2026] clarifies exactly when
value exceeds cost (`sharpRule`, a threshold), while [tsvilodub-etal-2026]
passes the margin through a logistic gate (a soft threshold; see
`TsvilodubEtAl2026.softGateRule`). `ClarifyRule` is the contract both
instantiate, exposing sharp vs. soft as a formal decision-rule choice.
-/

namespace Phenomena.Clarification

open Core.DecisionTheory BigOperators

/-- Maximum utility achievable at world `w` across actions.

    With Finset actions, this is `sup'` over utilities at world `w`. -/
def bestUtilityAt {W A : Type*} (dp : DecisionProblem W A)
    (actions : Finset A) (w : W) : ℚ :=
  if h : actions.Nonempty then actions.sup' h (dp.utility w) else 0

/-- Oracle value: expected utility under perfect information.
    `Σ_w P(w) · max_a U(w, a)` -/
def oracleValue {W A : Type*} [Fintype W] (dp : DecisionProblem W A)
    (actions : Finset A) : ℚ :=
  ∑ w : W, dp.prior w * bestUtilityAt dp actions w

/-- Expected value of perfect information (EVPI).

    EVPI = oracleValue − dpValue
         = Σ_w P(w) · max_a U(w,a) − max_a Σ_w P(w) · U(w,a)

    Equivalently, the expected regret of the current best action
    ([tsvilodub-etal-2026]), or the upper bound on VoI for any
    question ([dong-etal-2026]).

    [raiffa-schlaifer-1961] -/
def evpi {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A) : ℚ :=
  oracleValue dp actions - dpValue dp actions

-- ── Main theorem ─────────────────────────────────────────────────────

/-- EVPI is non-negative: acting with perfect information is at least
    as good as acting without.

    Proof sketch: For each action `a`, its expected utility `EU(a)` equals
    `Σ_w P(w) · U(w,a)`. The oracle value `Σ_w P(w) · max_a' U(w,a')`
    is pointwise ≥ `Σ_w P(w) · U(w,a)` since `max_a' U(w,a') ≥ U(w,a)`.
    Therefore `oracleValue ≥ EU(a)` for every `a`, hence
    `oracleValue ≥ max_a EU(a) = dpValue`. -/
theorem evpi_nonneg {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (actions : Finset A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hne : actions.Nonempty) :
    0 ≤ evpi dp actions := by
  unfold evpi
  suffices h : dpValue dp actions ≤ oracleValue dp actions by linarith
  -- dpValue = sup' of expectedUtility; show each EU(a) ≤ oracleValue
  unfold dpValue oracleValue
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

/-! ### The clarify-or-commit decision rule -/

/-- A clarify-or-commit decision rule: clarification propensity as a
monotone `[0, 1]`-valued function of the net value-of-information signal
(value minus cost). The shared contract of [dong-etal-2026]'s sharp
threshold and [tsvilodub-etal-2026]'s logistic gate. -/
structure ClarifyRule where
  /-- Clarification propensity given the net value signal. -/
  propensity : ℝ → ℝ
  mono : Monotone propensity
  nonneg : ∀ x, 0 ≤ propensity x
  le_one : ∀ x, propensity x ≤ 1

/-- The sharp-threshold rule: clarify exactly when the net value is
positive ([dong-etal-2026]'s `worthAsking`). -/
noncomputable def sharpRule : ClarifyRule where
  propensity x := if 0 < x then 1 else 0
  mono x y hxy := by
    show (if 0 < x then (1 : ℝ) else 0) ≤ if 0 < y then 1 else 0
    by_cases hx : 0 < x
    · rw [if_pos hx, if_pos (hx.trans_le hxy)]
    · rw [if_neg hx]
      split <;> norm_num
  nonneg x := by split <;> norm_num
  le_one x := by split <;> norm_num

theorem sharpRule_apply_of_pos {x : ℝ} (h : 0 < x) : sharpRule.propensity x = 1 :=
  if_pos h

theorem sharpRule_apply_of_nonpos {x : ℝ} (h : ¬ 0 < x) : sharpRule.propensity x = 0 :=
  if_neg h

/-- The sharp rule is binary — the formal signature of a threshold process,
against which soft gates contrast (`TsvilodubEtAl2026.softGateRule_apply_zero`). -/
theorem sharpRule_binary (x : ℝ) :
    sharpRule.propensity x = 0 ∨ sharpRule.propensity x = 1 := by
  by_cases hx : 0 < x
  · exact Or.inr (sharpRule_apply_of_pos hx)
  · exact Or.inl (sharpRule_apply_of_nonpos hx)

end Phenomena.Clarification
