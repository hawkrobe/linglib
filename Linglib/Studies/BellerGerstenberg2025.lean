import Linglib.Pragmatics.RSA.Operators
import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Semantics.Causation.Sufficiency
import Linglib.Semantics.Causation.Necessity
import Linglib.Semantics.Alternatives.Lexical
import Linglib.Semantics.Causation.ProductionDependence
import Mathlib.Data.Rat.Defs

/-!
# [beller-gerstenberg-2025]: Causation, Meaning, and Communication
[beller-gerstenberg-2025]

Formalizes Beller & Gerstenberg (2025) "Causation, Meaning, and Communication,"
*Psychological Review* 133(2), 339–381.

A counterfactual simulation model of causal language combining:

1. **Causal knowledge module**: computes whether-causation (W), how-causation (H),
   and sufficient-causation (S) from counterfactual simulations
2. **Semantics module**: defines four causal expressions as logical combinations
   of W, H, S (Eqs. 4–7)
3. **Pragmatics module**: RSA inference selects the most informative true expression

## Semantics (Eqs. 4–7)

- **affected**(A → e) = W ∨ H ∨ S  (any causal involvement)
- **enabled**(A → e) = W ∨ S  (necessity or sufficiency)
- **caused**(A → e) = H ∧ (W ∨ S) ∧_σ M ∧_σ U  (how-cause + counterfactual,
  softened by movement M and uniqueness U; σ controls softening)
- **made no difference**(A → e) = ¬W ∧ ¬_ν H ∧ ¬S  (no causal role,
  with soft negation ¬_ν of how-cause; ν controls softening)

The expressions form a hierarchy of specificity: caused ⊂ enabled ⊂ affected.
This hierarchy drives scalar implicatures via RSA pragmatic reasoning.

## Simplification

This formalization uses **Boolean** W, H, S (matching Table 1's illustrative
scenarios where aspect values are 0 or 1). The full paper computes W and S
as graded probabilities from noisy counterfactual simulations (Eqs. 1, 3).

The core Boolean semantics omit M (movement) and U (uniqueness), which only
affect "caused" via soft conjunction. These features are process constraints
that reduce the probability of "caused" when the candidate cause was
stationary (M=false) or not the unique contactor (U=false). For the
illustrative Table 1 scenarios, M=true and U=true throughout.

## Experiments

- **Experiment 1A**: Norming study (N=50). 15/20 sentence frames had median
  acceptability ≥ 4 (scale midpoint) for all three causal expressions.
- **Experiment 1B**: Semantic relations (N=53). Contradictory orderings
  (e.g., "caused but did not enable") rated less acceptable than consistent
  orderings (e.g., "affected but did not cause"). Confirms overlapping
  (not inconsistent) semantics for "caused" and "enabled."
- **Experiment 1C**: Implicature cancellation (N=51). "in fact" cancellations
  (e.g., "affected, in fact caused") rated more acceptable than redundant
  specifications (e.g., "caused, in fact affected").
- **Experiment 2**: Speaker task (N=62, 30 billiard scenarios). Full model
  r=0.87, RMSE=0.13. Fitted: θ=1.0, σ=0.65, ν=0.25, λ=40.18.
- **Experiment 3**: Listener task (N=50, 36 trials). Full model r=0.91,
  RMSE=0.10.

-/

set_option autoImplicit false

namespace BellerGerstenberg2025

open Intensional (WorldTimeIndex)
open scoped ENNReal


-- ============================================================================
-- Section 1: Causal Expressions
-- ============================================================================

/-- The four causal expressions studied in the paper (Figure 2, p. 343).

Participants chose among these to describe billiard-ball interactions:
1. "Ball A **caused** Ball B to go through the gate."
2. "Ball A **enabled** Ball B to go through the gate."
3. "Ball A **affected** Ball B's going through the gate."
4. "Ball A **made no difference** to Ball B's going through the gate." -/
inductive CausalExpression
  | caused
  | enabled
  | affected
  | madeNoDifference
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : Nonempty CausalExpression := ⟨.caused⟩


-- ============================================================================
-- Section 2: Causal Aspects and World State
-- ============================================================================

/-- Core causal aspects from the counterfactual simulation model (CSM).

- **W** (whether-causation): P(e' ≠ e | s, remove(A)). Was the cause
  counterfactually necessary? (Eq. 1)
- **H** (how-causation): P(Δe' ≠ Δe | s, change(A)). Did the cause affect
  the fine-grained outcome? Binary. (Eq. 2)
- **S** (sufficient-causation): P(W(A → e) | s, remove(¬A)). Would the cause
  have been a whether-cause if alternatives were removed? (Eq. 3) -/
structure CausalWorld where
  whether : Bool
  how : Bool
  sufficient : Bool
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CausalWorld where
  elems := {
    ⟨false, false, false⟩,
    ⟨false, false, true⟩,
    ⟨false, true, false⟩,
    ⟨false, true, true⟩,
    ⟨true, false, false⟩,
    ⟨true, false, true⟩,
    ⟨true, true, false⟩,
    ⟨true, true, true⟩
  }
  complete := by
    intro ⟨w, h, s⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, CausalWorld.mk.injEq]
    cases w <;> cases h <;> cases s <;> simp

instance : Nonempty CausalWorld := ⟨⟨false, false, false⟩⟩

instance : ToString CausalWorld where
  toString cw :=
    let w := if cw.whether then "W" else "¬W"
    let h := if cw.how then "H" else "¬H"
    let s := if cw.sufficient then "S" else "¬S"
    s!"({w}, {h}, {s})"


-- ============================================================================
-- Section 3: Boolean Semantics (Core)
-- ============================================================================

/-- Boolean semantics of causal expressions (Eqs. 4–7, pp. 346–347).

This is the **core** of the semantics, omitting the soft constraints
(σ for M/U in "caused", ν for H in "made no difference").

- affected: W ∨ H ∨ S — any causal involvement (Eq. 4)
- enabled: W ∨ S — necessity or sufficiency, not just how (Eq. 5)
- caused: H ∧ (W ∨ S) — how-cause plus counterfactual (core of Eq. 6)
- madeNoDifference: ¬W ∧ ¬H ∧ ¬S — no causal involvement (hard version of Eq. 7) -/
def expressionMeaning (cw : CausalWorld) : CausalExpression → Bool
  | .affected => cw.whether || cw.how || cw.sufficient
  | .enabled => cw.whether || cw.sufficient
  | .caused => cw.how && (cw.whether || cw.sufficient)
  | .madeNoDifference => !cw.whether && !cw.how && !cw.sufficient


-- ============================================================================
-- Section 4: Semantic Hierarchy
-- ============================================================================

/-- "caused" implies "enabled": H ∧ (W ∨ S) → W ∨ S.

"Caused" is the most specific expression (p. 349). -/
theorem caused_implies_enabled (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .enabled := by
  simp only [expressionMeaning, Bool.and_eq_true, Bool.or_eq_true]
  intro ⟨_, h_ws⟩; exact h_ws

/-- "enabled" implies "affected": W ∨ S → W ∨ H ∨ S. -/
theorem enabled_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .enabled → expressionMeaning cw .affected := by
  simp only [expressionMeaning]
  cases cw.whether <;> cases cw.how <;> cases cw.sufficient <;> decide

/-- Full scalar chain: caused → enabled → affected. -/
theorem caused_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .affected :=
  fun h => enabled_implies_affected cw (caused_implies_enabled cw h)

/-- "madeNoDifference" is the negation of "affected" (Boolean version). -/
theorem madeNoDifference_iff_not_affected (cw : CausalWorld) :
    expressionMeaning cw .madeNoDifference ↔ !expressionMeaning cw .affected := by
  simp only [expressionMeaning]
  cases cw.whether <;> cases cw.how <;> cases cw.sufficient <;> decide


-- ============================================================================
-- Section 5: Graded Semantics (Eqs. 4–7 with ν)
-- ============================================================================

/-- Graded semantics with soft negation parameter ν (Eq. 7, p. 347).

The full paper uses ν to soften the negation of H in "made no difference":
when H=true but W=false and S=false (Ball A is a how-cause only),
"made no difference" gets semantic value ν instead of 0.

For "caused," the full model also softens M (movement) and U (uniqueness)
via parameter σ (Eq. 6). Since the illustrative Table 1 scenarios all have
M=true and U=true, we omit these here — the core H ∧ (W ∨ S) suffices. -/
def gradedMeaning (cw : CausalWorld) (ν : ℚ) : CausalExpression → ℚ
  | .affected => if cw.whether || cw.how || cw.sufficient then 1 else 0
  | .enabled => if cw.whether || cw.sufficient then 1 else 0
  | .caused => if cw.how && (cw.whether || cw.sufficient) then 1 else 0
  | .madeNoDifference =>
    (if cw.whether then 0 else 1) *
    (if cw.how then ν else 1) *
    (if cw.sufficient then 0 else 1)


-- ============================================================================
-- Section 6: Table 1 — Illustrative Scenarios (p. 346)
-- ============================================================================

/-- Scenario 1: Classic Michottean launch. Ball A collides with stationary Ball B,
launching it through the gate. W=1, H=1, S=1. -/
def scenario1 : CausalWorld := ⟨true, true, true⟩

/-- Scenario 2: Ball A knocks a box out of Ball B's path. Ball B was already
heading toward the gate. W=1, H=0, S=1 (double prevention). -/
def scenario2 : CausalWorld := ⟨true, false, true⟩

/-- Scenario 3: Ball B is heading toward the gate on its own. Ball A comes up
from behind and pushes it along. W=0, H=1, S=0 (how-cause only). -/
def scenario3 : CausalWorld := ⟨false, true, false⟩

/-- Scenario 4: Ball A does not interact with Ball B at all. No causal
involvement. W=0, H=0, S=0. -/
def scenario4 : CausalWorld := ⟨false, false, false⟩

/-- Illustrative ν parameter for Table 1 (p. 348: "set to 0.2"). -/
def ν_table1 : ℚ := 1 / 5

-- Table 1b: Semantic values

theorem table1b_scenario1 :
    gradedMeaning scenario1 ν_table1 .madeNoDifference = 0 ∧
    gradedMeaning scenario1 ν_table1 .affected = 1 ∧
    gradedMeaning scenario1 ν_table1 .enabled = 1 ∧
    gradedMeaning scenario1 ν_table1 .caused = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem table1b_scenario2 :
    gradedMeaning scenario2 ν_table1 .madeNoDifference = 0 ∧
    gradedMeaning scenario2 ν_table1 .affected = 1 ∧
    gradedMeaning scenario2 ν_table1 .enabled = 1 ∧
    gradedMeaning scenario2 ν_table1 .caused = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- In an H-only world (Scenario 3), "made no difference" has non-zero
semantic value ν=1/5 due to soft negation (Eq. 7). This is the key
distinction from the hard Boolean semantics. -/
theorem table1b_scenario3 :
    gradedMeaning scenario3 ν_table1 .madeNoDifference = 1/5 ∧
    gradedMeaning scenario3 ν_table1 .affected = 1 ∧
    gradedMeaning scenario3 ν_table1 .enabled = 0 ∧
    gradedMeaning scenario3 ν_table1 .caused = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

theorem table1b_scenario4 :
    gradedMeaning scenario4 ν_table1 .madeNoDifference = 1 ∧
    gradedMeaning scenario4 ν_table1 .affected = 0 ∧
    gradedMeaning scenario4 ν_table1 .enabled = 0 ∧
    gradedMeaning scenario4 ν_table1 .caused = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide


-- ============================================================================
-- Section 7: PMF-face RSA model
-- ============================================================================

/-! [beller-gerstenberg-2025]'s pragmatics module as a mathlib-PMF
Frank-Goodman model [frank-goodman-2012]: the literal listener is uniform
on each expression's extension over the 8 causal worlds (Table 1c), the
pragmatic speaker normalises literal informativity over expressions
(α = 1, no cost; Table 1d), and the pragmatic listener is the Bayesian
posterior against the uniform world prior. The fitted model (Experiment 2)
uses λ = 40.18, but α = 1 suffices for the qualitative predictions. -/

/-- Boolean meaning in speaker argument order (expression first). -/
abbrev sem (u : CausalExpression) (cw : CausalWorld) : Bool := expressionMeaning cw u

private theorem ext_nonempty (u : CausalExpression) :
    (RSA.extensionOf sem u).Nonempty := by
  cases u <;> decide

/-- Literal listener `L0(·|u)`: uniform on the expression's extension. -/
noncomputable def L0 (u : CausalExpression) : PMF CausalWorld :=
  RSA.L0OfBoolMeaning sem u (ext_nonempty u)

/-- L0 mass at a world where the expression holds: inverse extension size. -/
private theorem L0_apply_of_true {u : CausalExpression} {cw : CausalWorld} (k : ℕ)
    (h : sem u cw = true) (hk : (RSA.extensionOf sem u).card = k) :
    L0 u cw = (k : ℝ≥0∞)⁻¹ := by
  rw [L0, RSA.L0OfBoolMeaning_apply_of_mem _ h, hk]

private theorem L0_apply_of_false {u : CausalExpression} {cw : CausalWorld}
    (h : sem u cw = false) :
    L0 u cw = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ (by simp [h])

private theorem L0_ne_zero {u : CausalExpression} {cw : CausalWorld}
    (h : sem u cw = true) : L0 u cw ≠ 0 :=
  (PMF.mem_support_iff _ _).mp ((RSA.mem_support_L0OfBoolMeaning_iff _ cw).mpr h)

private theorem s1_ne_zero (cw : CausalWorld) :
    ∑' u, (L0 u cw : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ 0 := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]
  obtain ⟨u, hu⟩ : ∃ u, sem u cw = true := by
    revert cw; decide
  intro h
  exact L0_ne_zero hu (Finset.sum_eq_zero_iff.mp h u (Finset.mem_univ _))

private theorem s1_ne_top (cw : CausalWorld) :
    ∑' u, (L0 u cw : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ ⊤ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun u _ => PMF.apply_ne_top _ _

/-- Pragmatic speaker `S1(·|cw) ∝ L0(cw|·)` (α = 1, zero cost; Table 1d). -/
noncomputable def S1 (cw : CausalWorld) : PMF CausalExpression :=
  RSA.S1Belief L0 (fun _ => 1) 1 cw (s1_ne_zero cw) (s1_ne_top cw)

/-- Uniform prior over the 8 causal worlds. -/
noncomputable def worldPrior : PMF CausalWorld := PMF.uniformOfFintype CausalWorld

private theorem marg_ne_zero {u : CausalExpression} (cw : CausalWorld)
    (h : sem u cw = true) :
    PMF.marginal S1 worldPrior u ≠ 0 :=
  PMF.marginal_ne_zero S1 worldPrior u
    ((worldPrior.mem_support_iff cw).mp (PMF.mem_support_uniformOfFintype cw))
    (RSA.S1Belief_apply_ne_zero_of_pos L0 _ 1 cw _ _ (L0_ne_zero h) one_ne_zero)

/-- Pragmatic listener `L1(·|u)`: Bayesian posterior of `S1` against the
uniform world prior. -/
noncomputable def L1 (u : CausalExpression) (h : PMF.marginal S1 worldPrior u ≠ 0) :
    PMF CausalWorld :=
  PMF.posterior S1 worldPrior u h

/-- Same-world expression preference reduces to comparing literal-listener
mass — the speaker's partition function cancels. -/
theorem S1_lt_iff (cw : CausalWorld) (u₁ u₂ : CausalExpression) :
    S1 cw u₁ < S1 cw u₂ ↔ L0 u₁ cw < L0 u₂ cw := by
  unfold S1
  rw [RSA.S1Belief_apply_lt_iff_score_lt]
  simp only [ENNReal.rpow_one, mul_one]

/-- `≤` companion of `S1_lt_iff`. -/
theorem S1_le_iff (cw : CausalWorld) (u₁ u₂ : CausalExpression) :
    S1 cw u₁ ≤ S1 cw u₂ ↔ L0 u₁ cw ≤ L0 u₂ cw := by
  unfold S1
  rw [RSA.S1Belief_apply_le_iff_score_le]
  simp only [ENNReal.rpow_one, mul_one]

/-- Cross-world vacuous zero: where the expression is false the speaker
assigns it no mass, so any world where it holds wins. -/
private theorem S1_lt_of_zero_pos {cw₁ cw₂ : CausalWorld} {u : CausalExpression}
    (h₁ : sem u cw₁ = false) (h₂ : sem u cw₂ = true) :
    S1 cw₁ u < S1 cw₂ u := by
  unfold S1 RSA.S1Belief
  exact PMF.normalize_lt_of_apply_zero_pos _ _ (s1_ne_zero cw₁) (s1_ne_top cw₁)
    (s1_ne_zero cw₂) (s1_ne_top cw₂) u
    (by simp only [ENNReal.rpow_one, mul_one]; exact L0_apply_of_false h₁)
    (by simp only [ENNReal.rpow_one, mul_one]; exact L0_ne_zero h₂)


-- ============================================================================
-- Section 8: PMF-face Predictions
-- ============================================================================

/-! ## S1 speaker predictions from the full 8-world Boolean model

These theorems verify that the PMF-face model reproduces the qualitative
predictions from Table 1d. The predictions arise from the full space of
2³ = 8 causal worlds with uniform prior and Boolean semantics: extension
sizes are caused 3, enabled 6, affected 7, madeNoDifference 1.

In each scenario, the pragmatic speaker selects the most informative
true expression, producing the same preference orderings as Table 1d. -/

/-- **Scenario 1 (full causation)**: S1 prefers "caused" over "enabled."

In (W=1, H=1, S=1), all positive expressions are literally true.
"caused" applies to only 3/8 worlds while "enabled" applies to 6/8,
so L0("caused") is more informative → S1 selects "caused." -/
theorem s1_cfg_full_caused_gt_enabled :
    S1 scenario1 .caused > S1 scenario1 .enabled := by
  rw [gt_iff_lt, S1_lt_iff, L0_apply_of_true 6 (by decide) (by decide),
    L0_apply_of_true 3 (by decide) (by decide)]
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

/-- **Scenario 1**: S1 prefers "enabled" over "affected." -/
theorem s1_cfg_full_enabled_gt_affected :
    S1 scenario1 .enabled > S1 scenario1 .affected := by
  rw [gt_iff_lt, S1_lt_iff, L0_apply_of_true 7 (by decide) (by decide),
    L0_apply_of_true 6 (by decide) (by decide)]
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

/-- **Scenario 2 (double prevention)**: S1 prefers "enabled" over "affected."

In (W=1, H=0, S=1), "caused" is literally false (H=0), so the speaker
chooses between "enabled" and "affected." "enabled" is more informative
(6/8 vs 7/8 worlds), so S1 selects it. -/
theorem s1_cfg_double_prevention_enabled_gt_affected :
    S1 scenario2 .enabled > S1 scenario2 .affected := by
  rw [gt_iff_lt, S1_lt_iff, L0_apply_of_true 7 (by decide) (by decide),
    L0_apply_of_true 6 (by decide) (by decide)]
  exact ENNReal.inv_lt_inv.mpr (by norm_num)

/-- **Scenario 2**: "caused" is ruled out (literally false at H=0). -/
theorem s1_cfg_double_prevention_caused_zero :
    ¬(S1 scenario2 .caused > S1 scenario2 .enabled) := by
  rw [gt_iff_lt, not_lt, S1_le_iff, L0_apply_of_false (by decide)]
  exact zero_le

/-- **Scenario 3 (H-only)**: S1 prefers "affected" over "caused."

In (W=0, H=1, S=0), "affected" is the only true positive expression.
"caused" requires H ∧ (W ∨ S), which fails when W=S=0. -/
theorem s1_cfg_howOnly_affected_gt_caused :
    S1 scenario3 .affected > S1 scenario3 .caused := by
  rw [gt_iff_lt, S1_lt_iff, L0_apply_of_false (by decide)]
  exact pos_iff_ne_zero.mpr (L0_ne_zero (by decide))

/-- **Scenario 3**: "affected" also beats "madeNoDifference."

In the Boolean model (unlike the graded model with ν), "madeNoDifference"
is strictly false in an H-only world: ¬W ∧ ¬H ∧ ¬S fails because H=1. -/
theorem s1_cfg_howOnly_affected_gt_noDiff :
    S1 scenario3 .affected > S1 scenario3 .madeNoDifference := by
  rw [gt_iff_lt, S1_lt_iff, L0_apply_of_false (by decide)]
  exact pos_iff_ne_zero.mpr (L0_ne_zero (by decide))

/-- **Scenario 4 (no causation)**: S1 prefers "madeNoDifference" over "affected."

In (W=0, H=0, S=0), only "madeNoDifference" is literally true. -/
theorem s1_cfg_noCause_noDiff_gt_affected :
    S1 scenario4 .madeNoDifference > S1 scenario4 .affected := by
  rw [gt_iff_lt, S1_lt_iff, L0_apply_of_false (by decide)]
  exact pos_iff_ne_zero.mpr (L0_ne_zero (by decide))

/-! ## L1 listener predictions: scalar implicature effects

The pragmatic listener (L1) inverts S1 via Bayes' rule. Hearing a weaker
expression triggers a scalar implicature: the listener infers the speaker
*chose not* to use a stronger expression, shifting probability away from
worlds where the stronger expression would have been true.

Each comparison cancels the shared marginal and uniform prior
(`PMF.posterior_lt_iff_kernel_lt_of_uniform`), reducing to a cross-world
`S1` comparison: a vacuous zero where the expression is false, or a
partition-dominance where the literal weights agree. -/

theorem marg_caused : PMF.marginal S1 worldPrior .caused ≠ 0 :=
  marg_ne_zero scenario1 (by decide)

theorem marg_enabled : PMF.marginal S1 worldPrior .enabled ≠ 0 :=
  marg_ne_zero scenario1 (by decide)

theorem marg_noDiff : PMF.marginal S1 worldPrior .madeNoDifference ≠ 0 :=
  marg_ne_zero scenario4 (by decide)

/-- **L1 hearing "caused"**: higher probability for full-causation world
than no-causation world.

L1("caused") assigns positive mass only to worlds where "caused" is
literally true (H ∧ (W ∨ S)). The no-causation world (F,F,F) gets zero. -/
theorem l1_cfg_caused_identifies_full :
    L1 .caused marg_caused scenario1 > L1 .caused marg_caused scenario4 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_lt_of_zero_pos (by decide) (by decide)

/-! Speaker partition functions at the two "enabled"-worlds: at (T,F,F) only
"enabled" and "affected" are true (`Z = 6⁻¹ + 7⁻¹`); at (T,T,T) "caused" also
competes (`Z = 3⁻¹ + 6⁻¹ + 7⁻¹`). The smaller partition means a sharper
speaker, so hearing "enabled" favours (T,F,F). -/

private theorem sumExpr (f : CausalExpression → ℝ≥0∞) :
    ∑' u, f u = f .caused + f .enabled + f .affected + f .madeNoDifference := by
  rw [tsum_fintype,
    show (Finset.univ : Finset CausalExpression)
      = {.caused, .enabled, .affected, .madeNoDifference} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem Z_TFF :
    (∑' u, (L0 u ⟨true, false, false⟩ : ℝ≥0∞) ^ (1 : ℝ) * 1) = 6⁻¹ + 7⁻¹ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [sumExpr, L0_apply_of_false (by decide), L0_apply_of_true 6 (by decide) (by decide),
    L0_apply_of_true 7 (by decide) (by decide), L0_apply_of_false (by decide)]
  push_cast
  ring

private theorem Z_TTT :
    (∑' u, (L0 u scenario1 : ℝ≥0∞) ^ (1 : ℝ) * 1) = 3⁻¹ + 6⁻¹ + 7⁻¹ := by
  simp only [ENNReal.rpow_one, mul_one]
  rw [sumExpr, L0_apply_of_true 3 (by decide) (by decide),
    L0_apply_of_true 6 (by decide) (by decide),
    L0_apply_of_true 7 (by decide) (by decide), L0_apply_of_false (by decide)]
  push_cast
  ring

/-- **L1 scalar implicature for "enabled"**: hearing "enabled" makes the
listener prefer worlds where "caused" is *false* over worlds where it's true.

Both (T,F,F) and (T,T,T) make "enabled" literally true (W ∨ S). But at
(T,T,T), S1 would have said "caused" instead (more informative), so
L1 down-weights (T,T,T) upon hearing "enabled." This is the classic
scalar implicature: "enabled" ⇝ ¬caused. -/
theorem l1_cfg_enabled_implicature :
    L1 .enabled marg_enabled ⟨true, false, false⟩ > L1 .enabled marg_enabled scenario1 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  unfold S1 RSA.S1Belief
  refine PMF.normalize_lt_of_apply_eq_of_sum_lt _ _ (s1_ne_zero scenario1)
    (s1_ne_top scenario1) (s1_ne_zero ⟨true, false, false⟩)
    (s1_ne_top ⟨true, false, false⟩) .enabled
    (by simp only [ENNReal.rpow_one, mul_one]
        rw [L0_apply_of_true 6 (by decide) (by decide),
          L0_apply_of_true 6 (by decide) (by decide)])
    (by simp only [ENNReal.rpow_one, mul_one]
        rw [L0_apply_of_true 6 (by decide) (by decide)]
        exact ENNReal.inv_ne_zero.mpr (by norm_num))
    (by simp only [ENNReal.rpow_one, mul_one]
        rw [L0_apply_of_true 6 (by decide) (by decide)]
        exact ENNReal.inv_ne_top.mpr (by norm_num))
    ?_
  rw [Z_TFF, Z_TTT, show (3 : ℝ≥0∞)⁻¹ + 6⁻¹ + 7⁻¹ = 6⁻¹ + 7⁻¹ + 3⁻¹ from by ring]
  exact ENNReal.lt_add_right
    (ENNReal.add_ne_top.mpr ⟨ENNReal.inv_ne_top.mpr (by norm_num),
      ENNReal.inv_ne_top.mpr (by norm_num)⟩)
    (ENNReal.inv_ne_zero.mpr (by norm_num))

/-- **L1 hearing "madeNoDifference"**: identifies the no-causation world.

"madeNoDifference" is true only at (F,F,F), so L1 assigns it probability 1. -/
theorem l1_cfg_noDiff_identifies_none :
    L1 .madeNoDifference marg_noDiff scenario4 > L1 .madeNoDifference marg_noDiff scenario1 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_lt_of_zero_pos (by decide) (by decide)


-- ============================================================================
-- Section 9: World-Specific Truth Values
-- ============================================================================

/-- Canonical test worlds -/
def world_W_only : CausalWorld := ⟨true, false, false⟩
def world_S_only : CausalWorld := ⟨false, false, true⟩
def world_H_only : CausalWorld := ⟨false, true, false⟩
def world_full : CausalWorld := ⟨true, true, true⟩
def world_none : CausalWorld := ⟨false, false, false⟩
def world_caused : CausalWorld := ⟨true, true, false⟩

/-- In W-only world, "enabled" is true but "caused" is false.
Speaker would use "enabled" (Scenario 2-like). -/
theorem W_only_enabled_not_caused :
    expressionMeaning world_W_only .enabled = true ∧
    expressionMeaning world_W_only .caused = false := by
  constructor <;> native_decide

/-- In H-only world, only "affected" applies among the positive expressions. -/
theorem H_only_affected_only :
    expressionMeaning world_H_only .affected = true ∧
    expressionMeaning world_H_only .enabled = false ∧
    expressionMeaning world_H_only .caused = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- In full world, all positive expressions apply. -/
theorem full_world_all_true :
    expressionMeaning world_full .affected = true ∧
    expressionMeaning world_full .enabled = true ∧
    expressionMeaning world_full .caused = true ∧
    expressionMeaning world_full .madeNoDifference = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- In none world, only "madeNoDifference" applies. -/
theorem none_world_only_negative :
    expressionMeaning world_none .affected = false ∧
    expressionMeaning world_none .enabled = false ∧
    expressionMeaning world_none .caused = false ∧
    expressionMeaning world_none .madeNoDifference = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide


-- ============================================================================
-- Section 10: Experiment 2 Results (pp. 358–362)
-- ============================================================================

/-- Fitted model parameters from Experiment 2 (p. 358, MLE).

θ=1.0 (counterfactual noise), σ=0.65 (softening for M/U in "caused"),
ν=0.25 (softening for H in "made no difference"), λ=40.18 (RSA speaker
optimality). -/
structure FittedParams where
  θ : ℚ      -- counterfactual simulation noise
  σ : ℚ      -- soft conjunction parameter for M, U
  ν : ℚ      -- soft negation parameter for H
  alpha : ℚ  -- RSA speaker optimality (λ in the paper)
  deriving Repr

def exp2_params : FittedParams :=
  { θ := 1, σ := 65/100, ν := 1/4, alpha := 4018/100 }

/-- Experiment 2 cross-validation (Table 8, p. 362). -/
structure CrossValidation where
  model : String
  r_median : ℚ
  rmse_median : ℚ
  deriving Repr

def exp2_fullModel : CrossValidation :=
  { model := "Full model", r_median := 87/100, rmse_median := 13/100 }

def exp2_noPragmatics : CrossValidation :=
  { model := "No pragmatics", r_median := 74/100, rmse_median := 18/100 }

def exp2_noSemNoPrag : CrossValidation :=
  { model := "No sem & no prag", r_median := 53/100, rmse_median := 25/100 }

/-- Full model outperforms alternatives in Experiment 2. -/
theorem exp2_full_best :
    exp2_fullModel.r_median > exp2_noPragmatics.r_median ∧
    exp2_fullModel.r_median > exp2_noSemNoPrag.r_median ∧
    exp2_fullModel.rmse_median < exp2_noPragmatics.rmse_median := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Experiment 3 cross-validation (Table 9, p. 366). -/
def exp3_fullModel : CrossValidation :=
  { model := "Full model", r_median := 91/100, rmse_median := 10/100 }

def exp3_noPragmatics : CrossValidation :=
  { model := "No pragmatics", r_median := 83/100, rmse_median := 13/100 }

/-- Full model outperforms in Experiment 3 (listener task). -/
theorem exp3_full_best :
    exp3_fullModel.r_median > exp3_noPragmatics.r_median ∧
    exp3_fullModel.rmse_median < exp3_noPragmatics.rmse_median := by
  constructor <;> native_decide


-- ============================================================================
-- Section 11: Bridge to Structural Causal Models
-- ============================================================================

/-! ## Bridge to Causation

Beller & Gerstenberg's W, H, S dimensions can be COMPUTED from structural
causal models, grounding the primitive Boolean features in the counterfactual
reasoning machinery of `Causation`.

| B&G aspect | Structural definition |
|------------|---------------------|
| W (whether) | `causallyNecessary` — would effect still occur without cause? |
| H (how) | `hasDirectLaw` — does a causal law directly connect cause to effect? |
| S (sufficient) | `causallySufficient` — does adding cause guarantee effect? |

The mapping of H to `hasDirectLaw` is an approximation. B&G's how-causation
(Eq. 2) tests whether the fine-grained outcome would differ under a small
perturbation of the cause, which is a richer notion than structural directness.
For simple causal models, the two coincide.
-/

section StructuralBridge

open Causation Causation.Mechanism Causation.SEM
open Causation.BoolSEM (causallySufficient causallyNecessary hasDirectLaw)

/-- Vertex enum for B&G's bridge models.
    `cause`, `alt`, `effect`, `intermediate` — covers solo, overdetermination, chain. -/
inductive BGVar | cause | alt | effect | intermediate
  deriving DecidableEq, Fintype, Repr

def bgVarList : List BGVar := [.cause, .alt, .intermediate, .effect]

-- ── Solo model: cause → effect (direct) ──

def soloGraph : CausalGraph BGVar :=
  ⟨fun | .cause => ∅ | .alt => ∅ | .intermediate => ∅ | .effect => {.cause}⟩

noncomputable def soloModel : BoolSEM BGVar :=
  { graph := soloGraph
    mech := fun v => match v with
      | .cause | .alt | .intermediate => const (G := soloGraph) false
      | .effect => deterministic (fun ρ => ρ ⟨.cause, by simp [soloGraph]⟩) }

noncomputable instance : SEM.IsDeterministic soloModel where
  mech_det v := match v with
    | .cause | .alt | .intermediate =>
      inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .effect => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

-- ── Overdetermination model: cause ∨ alt → effect, with alt in bg ──

def overdetGraph : CausalGraph BGVar :=
  ⟨fun | .cause => ∅ | .alt => ∅ | .intermediate => ∅
       | .effect => {.cause, .alt}⟩

noncomputable def overdetModel : BoolSEM BGVar :=
  { graph := overdetGraph
    mech := fun v => match v with
      | .cause | .alt | .intermediate => const (G := overdetGraph) false
      | .effect => deterministic (fun ρ =>
          ρ ⟨.cause, by simp [overdetGraph]⟩ || ρ ⟨.alt, by simp [overdetGraph]⟩) }

noncomputable instance : SEM.IsDeterministic overdetModel where
  mech_det v := match v with
    | .cause | .alt | .intermediate =>
      inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .effect => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

noncomputable def overdetBg : Valuation (fun _ : BGVar => Bool) :=
  Valuation.empty.extend .alt true

-- ── Chain model: cause → intermediate → effect ──

def chainGraph : CausalGraph BGVar :=
  ⟨fun | .cause => ∅ | .alt => ∅
       | .intermediate => {.cause}
       | .effect => {.intermediate}⟩

noncomputable def chainModel : BoolSEM BGVar :=
  { graph := chainGraph
    mech := fun v => match v with
      | .cause | .alt => const (G := chainGraph) false
      | .intermediate => deterministic (fun ρ => ρ ⟨.cause, by simp [chainGraph]⟩)
      | .effect => deterministic (fun ρ => ρ ⟨.intermediate, by simp [chainGraph]⟩) }

noncomputable instance : SEM.IsDeterministic chainModel where
  mech_det v := match v with
    | .cause | .alt =>
      inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .intermediate | .effect =>
      inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

-- ── DAG instances ──

/-- Depth function for `BGVar`: roots at 0, intermediate at 1, effect at 2.
    Strictly increases along every parent edge in all three BG2025 graphs
    (`soloGraph`, `overdetGraph`, `chainGraph`), so `IsDAG.of_depth`
    discharges acyclicity uniformly. -/
def bgDepth : BGVar → ℕ
  | .cause => 0
  | .alt => 0
  | .intermediate => 1
  | .effect => 2

/-- The ranking certificate for the solo graph, consumed by the `IsDAG`
    instance and the fuel bridges. -/
def soloRanking : CausalGraph.Ranking soloGraph :=
  ⟨bgDepth, fun {u v} h => by revert h; cases u <;> cases v <;> decide⟩

instance soloGraph_isDAG : CausalGraph.IsDAG soloGraph := soloRanking.isDAG

instance overdetGraph_isDAG : CausalGraph.IsDAG overdetGraph :=
  CausalGraph.IsDAG.of_depth overdetGraph bgDepth (by
    intro u v h
    cases v <;> simp [overdetGraph, CausalGraph.parents] at h <;>
      rcases h with h | h <;> subst h <;> decide)

instance chainGraph_isDAG : CausalGraph.IsDAG chainGraph :=
  CausalGraph.IsDAG.of_depth chainGraph bgDepth (by
    intro u v h
    cases v <;> simp [chainGraph, CausalGraph.parents] at h <;>
      subst h <;> decide)

noncomputable instance : CausalGraph.IsDAG soloModel.graph := soloGraph_isDAG
noncomputable instance : CausalGraph.IsDAG overdetModel.graph := overdetGraph_isDAG
noncomputable instance : CausalGraph.IsDAG chainModel.graph := chainGraph_isDAG

/-- Compute a `CausalWorld` from a V2 BoolSEM. W = causally necessary,
    H = direct law in graph, S = causally sufficient. -/
noncomputable def causalWorldFromModel {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation (fun _ : V => Bool))
    (cause effect : V) : CausalWorld :=
  { whether := decide (causallyNecessary M bg cause effect)
  , how := decide (hasDirectLaw M cause effect)
  , sufficient := decide (causallySufficient M bg cause effect) }

end StructuralBridge


-- ============================================================================
-- Section 12: Horn Scale
-- ============================================================================

section HornScaleBridge

open Alternatives

/-- The causal expression Horn scale: ⟨affected, enabled, caused⟩.

Ordered from weakest (true in most scenarios) to strongest (true in fewest).
"madeNoDifference" is excluded: it is the Boolean complement of "affected"
(proved in `madeNoDifference_iff_not_affected`), not a weaker scalar
alternative. -/
def causalScale : HornScale CausalExpression :=
  ⟨[.affected, .enabled, .caused]⟩

/-- Using "affected" implicates ¬enabled ∧ ¬caused (Experiment 1C). -/
theorem affected_alternatives :
    strongerAlternatives causalScale .affected = [.enabled, .caused] := by
  native_decide

/-- Using "enabled" implicates ¬caused. -/
theorem enabled_alternatives :
    strongerAlternatives causalScale .enabled = [.caused] := by native_decide

/-- Scale ordering is grounded in semantic entailment: stronger expressions
entail weaker ones at every world. This is the defining property of a
Horn scale — the scale structure isn't stipulated, it's *derived* from
the entailment relations proved in Section 4. -/
theorem scale_grounded_in_entailment (cw : CausalWorld) :
    (expressionMeaning cw .caused → expressionMeaning cw .enabled) ∧
    (expressionMeaning cw .enabled → expressionMeaning cw .affected) :=
  ⟨caused_implies_enabled cw, enabled_implies_affected cw⟩

end HornScaleBridge


-- ============================================================================
-- Section 13: End-to-End Argumentation Chains
-- ============================================================================

/-! ## Structural Model → Causation Type → Expression → S1

Each theorem below chains across three levels of analysis:

1. **Structural**: A `BoolSEM` (structural equation model) yields
   directness and necessity via `hasDirectLaw` / `causallyNecessary`
2. **Causation type**: These determine production vs dependence
   causation via `causationType` (from `ProductionDependence.lean`)
3. **Semantic + Pragmatic**: The derived `CausalWorld` determines which
   expressions are literally true, and the S1 pragmatic speaker selects
   the most informative one

These are the deepest integration points: a change to `normalDevelopment`,
`expressionMeaning`, or the L0/S1 computation would break these theorems. -/

section EndToEnd

open Causation
open Causation.ProductionDependence (causationType)

/-! End-to-end pipeline theorems linking V2 BoolSEM models to RSA S1
    predictions. `causationType` (from `ProductionDependence.lean`)
    takes plain Bools, so its inputs are computed with the SEM
    predicates and passed through. -/

open Causation Causation.SEM
open Causation.BoolSEM (causallySufficient causallyNecessary hasDirectLaw)

private lemma solo_entails_iff {s : Valuation (fun _ : BGVar => Bool)}
    {v : BGVar} {x : Bool} :
    SEM.causallyEntails soloModel s v x ↔
      SEM.developDetVtxFuel soloModel s 3 v = some x :=
  SEM.causallyEntails_iff_fuel soloModel soloRanking (by cases v <;> decide) s x

private lemma solo_necessary_iff {bg : Valuation (fun _ : BGVar => Bool)}
    {c e : BGVar} :
    causallyNecessary soloModel bg c e ↔
      SEM.causallyNecessaryFuel soloModel 3 bg c true e true :=
  SEM.causallyNecessary_iff_fuel soloModel soloRanking
    (by intro v; cases v <;> decide) bg c true e true

set_option maxRecDepth 100000 in
/-- The solo model computes the full-profile world `⟨W,H,S⟩ = ⟨1,1,1⟩`:
    Def 10b necessity and bare sufficiency proven through the fuel
    bridge, then converted into the `decide`-wrapped Bools. -/
theorem solo_causalWorld :
    causalWorldFromModel soloModel Valuation.empty .cause .effect =
      { whether := true, how := true, sufficient := true } := by
  have hNec : causallyNecessary soloModel Valuation.empty .cause .effect :=
    solo_necessary_iff.mpr (by decide)
  have hSuf : causallySufficient soloModel Valuation.empty .cause .effect :=
    SEM.causallySufficient_of_causallyEntails (solo_entails_iff.mpr (by decide))
  have hDir : hasDirectLaw soloModel .cause .effect := by decide
  unfold causalWorldFromModel
  rw [decide_eq_true hNec, decide_eq_true hSuf, decide_eq_true hDir]

/-- **Solo cause → S1 prefers "caused".**
    From a V2 model with one direct law (cause → effect), the pipeline
    produces the correct pragmatic prediction. -/
theorem solo_cause_chain :
    let cw := causalWorldFromModel soloModel Valuation.empty .cause .effect
    expressionMeaning cw .caused = true ∧
    S1 cw .caused > S1 cw .enabled ∧
    S1 cw .caused > S1 cw .affected := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [solo_causalWorld]
  · decide
  · exact s1_cfg_full_caused_gt_enabled
  · rw [gt_iff_lt, S1_lt_iff, L0_apply_of_true 7 (by decide) (by decide),
      L0_apply_of_true 3 (by decide) (by decide)]
    exact ENNReal.inv_lt_inv.mpr (by norm_num)

end EndToEnd


-- ════════════════════════════════════════════════════
-- § Experimental Data (Figure 2, Tables 8–9)
-- ════════════════════════════════════════════════════

/-! ## Overall Acceptance Rates (Figure 2)

Proportion of "Yes" (Accurate) responses by verb.
Ordering: caused > made > forced.

Rates stored as percentages (Nat) to avoid heavy Mathlib imports. -/

/-- An experimental observation: verb form paired with acceptance rate (%). -/
structure AcceptanceRate where
  verb : String
  ratePct : Nat      -- Proportion of "Yes" responses (percentage)
  deriving Repr, DecidableEq

def causedRate : AcceptanceRate := { verb := "caused", ratePct := 48 }
def madeRate : AcceptanceRate := { verb := "made", ratePct := 40 }
def forcedRate : AcceptanceRate := { verb := "forced", ratePct := 35 }

/-- Acceptance ordering: *caused* > *made* > *forced* (Figure 2). -/
theorem acceptance_ordering :
    causedRate.ratePct > madeRate.ratePct ∧
    madeRate.ratePct > forcedRate.ratePct := by decide

/-! ## Main Effect Coefficients (Table 8)

Bayesian logistic regression with verb × SUFresidALT × INT × ALT.

Coefficients stored as (numerator, denominator=100) to avoid ℚ imports. -/

/-- A regression coefficient with its 95% credible interval.
Values are × 100 (e.g., 119 means 1.19). -/
structure Coefficient where
  name : String
  estimate100 : Int   -- Estimate × 100
  lowerCI100 : Int    -- Lower 95% CI × 100
  upperCI100 : Int    -- Upper 95% CI × 100
  deriving Repr, DecidableEq

/-- A coefficient is reliable when its 95% CI excludes 0. -/
def Coefficient.isReliable (c : Coefficient) : Bool :=
  (c.lowerCI100 > 0 && c.upperCI100 > 0) || (c.lowerCI100 < 0 && c.upperCI100 < 0)

def coeff_sufResidAlt : Coefficient :=
  { name := "SUFresidALT", estimate100 := 119, lowerCI100 := 89, upperCI100 := 150 }

def coeff_int : Coefficient :=
  { name := "INT", estimate100 := 54, lowerCI100 := 28, upperCI100 := 81 }

def coeff_alt : Coefficient :=
  { name := "ALT", estimate100 := -82, lowerCI100 := -111, upperCI100 := -55 }

theorem suf_reliable : coeff_sufResidAlt.isReliable = true := by native_decide
theorem int_reliable : coeff_int.isReliable = true := by native_decide
theorem alt_reliable : coeff_alt.isReliable = true := by native_decide

/-- SUF has the largest absolute main effect. -/
theorem suf_largest_main_effect :
    coeff_sufResidAlt.estimate100 > coeff_int.estimate100 ∧
    coeff_sufResidAlt.estimate100 > -coeff_alt.estimate100 := by decide

/-- ALT has a negative main effect (more alternatives → less acceptable). -/
theorem alt_negative : coeff_alt.estimate100 < 0 := by decide

/-! ## Per-Verb Interaction Reliability (Table 9)

Estimates of interaction intercepts by verb. -/

/-- Per-verb reliable interaction from Table 9. -/
structure VerbInteraction where
  verb : String
  interaction : String
  positive : Bool   -- CI entirely above 0
  deriving Repr

/-- *made* uniquely has a reliable SUFresidALT×INT interaction (Table 9). -/
def made_sufInt : VerbInteraction :=
  { verb := "made", interaction := "SUFresidALT:INT", positive := true }

/-- All verbs share reliable SUFresidALT×ALT interaction. -/
def caused_sufAlt : VerbInteraction :=
  { verb := "caused", interaction := "SUFresidALT:ALT", positive := true }
def made_sufAlt : VerbInteraction :=
  { verb := "made", interaction := "SUFresidALT:ALT", positive := true }
def forced_sufAlt : VerbInteraction :=
  { verb := "forced", interaction := "SUFresidALT:ALT", positive := true }

/-- All verbs share reliable INT×ALT interaction. -/
def caused_intAlt : VerbInteraction :=
  { verb := "caused", interaction := "INT:ALT", positive := true }
def made_intAlt : VerbInteraction :=
  { verb := "made", interaction := "INT:ALT", positive := true }
def forced_intAlt : VerbInteraction :=
  { verb := "forced", interaction := "INT:ALT", positive := true }

/-! ## Acceptability Contrasts

Non-interchangeability of causative verbs across contexts. -/

/-- Acceptability judgment for a causative verb in context. -/
inductive Acceptability where
  | acceptable       -- ✓
  | marginal         -- ?
  | unacceptable     -- *
  deriving DecidableEq, Repr

/-- A single acceptability judgment: verb + context + status. -/
structure CausativeJudgment where
  verb : String
  context : String
  judgment : Acceptability
  source : String  -- Paper example number
  deriving Repr

/-- Low sufficiency, low intention context: only *cause* is acceptable. -/
def ex_lowSuf_caused : CausativeJudgment :=
  { verb := "caused", context := "go to gym by mentioning how habit helped"
  , judgment := .acceptable, source := "low-SUF scenario" }
def ex_lowSuf_made : CausativeJudgment :=
  { verb := "made", context := "go to gym by mentioning how habit helped"
  , judgment := .unacceptable, source := "low-SUF scenario" }
def ex_lowSuf_forced : CausativeJudgment :=
  { verb := "forced", context := "go to gym by mentioning how habit helped"
  , judgment := .unacceptable, source := "low-SUF scenario" }

/-- High sufficiency, high intention, low alternatives: all verbs acceptable. -/
def ex_highAll_caused : CausativeJudgment :=
  { verb := "caused", context := "go to gym by holding child hostage"
  , judgment := .acceptable, source := "high-SUF/INT scenario" }
def ex_highAll_made : CausativeJudgment :=
  { verb := "made", context := "go to gym by holding child hostage"
  , judgment := .acceptable, source := "high-SUF/INT scenario" }
def ex_highAll_forced : CausativeJudgment :=
  { verb := "forced", context := "go to gym by holding child hostage"
  , judgment := .acceptable, source := "high-SUF/INT scenario" }

/-- In high-SUF, high-INT, low-ALT contexts, all three verbs are acceptable. -/
theorem all_acceptable_high_suf_int_low_alt :
    ex_highAll_caused.judgment = .acceptable ∧
    ex_highAll_made.judgment = .acceptable ∧
    ex_highAll_forced.judgment = .acceptable := by decide

/-- In low-SUF contexts, only *cause* is acceptable. -/
theorem only_cause_low_suf :
    ex_lowSuf_caused.judgment = .acceptable ∧
    ex_lowSuf_made.judgment = .unacceptable ∧
    ex_lowSuf_forced.judgment = .unacceptable := by decide

end BellerGerstenberg2025
