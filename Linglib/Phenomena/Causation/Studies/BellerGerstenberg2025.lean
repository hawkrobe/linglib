import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Alternatives.Lexical
import Linglib.Theories.Semantics.Causation.ProductionDependence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Defs

/-!
# @cite{beller-gerstenberg-2025}: Causation, Meaning, and Communication
@cite{beller-gerstenberg-2025}

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

open Core (WorldTimeIndex)


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
-- Section 7: RSAConfig
-- ============================================================================

open RSA Real in
/-- @cite{beller-gerstenberg-2025} causal expression model as RSAConfig.

Meaning: Boolean expression semantics (1 if true, 0 if false).
World prior: uniform over the 8 possible W-H-S worlds.
S1 score: belief-based (rpow): score = L0(w|u)^α.
α = 1 for the illustrative Table 1 computation.

The fitted model (Experiment 2) uses λ=40.18, but α=1 suffices for
the qualitative predictions and matches Table 1d. -/
noncomputable def cfg : RSAConfig CausalExpression CausalWorld where
  meaning _ _ u cw := if expressionMeaning cw u then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg _ := by positivity


-- ============================================================================
-- Section 8: RSAConfig Predictions (rsa_predict)
-- ============================================================================

/-! ## S1 speaker predictions from the full 8-world Boolean model

These theorems verify that the RSAConfig reproduces the qualitative
predictions from Table 1d using `rsa_predict`. The predictions arise
from the full space of 2³ = 8 causal worlds with uniform prior and
Boolean semantics.

In each scenario, the pragmatic speaker selects the most informative
true expression, producing the same preference orderings as Table 1d. -/

/-- **Scenario 1 (full causation)**: S1 prefers "caused" over "enabled."

In (W=1, H=1, S=1), all positive expressions are literally true.
"caused" applies to only 3/8 worlds while "enabled" applies to 6/8,
so L0("caused") is more informative → S1 selects "caused." -/
theorem s1_cfg_full_caused_gt_enabled :
    cfg.S1 () scenario1 .caused > cfg.S1 () scenario1 .enabled := by
  rsa_predict

/-- **Scenario 1**: S1 prefers "enabled" over "affected." -/
theorem s1_cfg_full_enabled_gt_affected :
    cfg.S1 () scenario1 .enabled > cfg.S1 () scenario1 .affected := by
  rsa_predict

/-- **Scenario 2 (double prevention)**: S1 prefers "enabled" over "affected."

In (W=1, H=0, S=1), "caused" is literally false (H=0), so the speaker
chooses between "enabled" and "affected." "enabled" is more informative
(6/8 vs 7/8 worlds), so S1 selects it. -/
theorem s1_cfg_double_prevention_enabled_gt_affected :
    cfg.S1 () scenario2 .enabled > cfg.S1 () scenario2 .affected := by
  rsa_predict

/-- **Scenario 2**: "caused" is ruled out (literally false at H=0). -/
theorem s1_cfg_double_prevention_caused_zero :
    ¬(cfg.S1 () scenario2 .caused > cfg.S1 () scenario2 .enabled) := by
  rsa_predict

/-- **Scenario 3 (H-only)**: S1 prefers "affected" over "caused."

In (W=0, H=1, S=0), "affected" is the only true positive expression.
"caused" requires H ∧ (W ∨ S), which fails when W=S=0. -/
theorem s1_cfg_howOnly_affected_gt_caused :
    cfg.S1 () scenario3 .affected > cfg.S1 () scenario3 .caused := by
  rsa_predict

/-- **Scenario 3**: "affected" also beats "madeNoDifference."

In the Boolean model (unlike the graded model with ν), "madeNoDifference"
is strictly false in an H-only world: ¬W ∧ ¬H ∧ ¬S fails because H=1. -/
theorem s1_cfg_howOnly_affected_gt_noDiff :
    cfg.S1 () scenario3 .affected > cfg.S1 () scenario3 .madeNoDifference := by
  rsa_predict

/-- **Scenario 4 (no causation)**: S1 prefers "madeNoDifference" over "affected."

In (W=0, H=0, S=0), only "madeNoDifference" is literally true. -/
theorem s1_cfg_noCause_noDiff_gt_affected :
    cfg.S1 () scenario4 .madeNoDifference > cfg.S1 () scenario4 .affected := by
  rsa_predict

/-! ## L1 listener predictions: scalar implicature effects

The pragmatic listener (L1) inverts S1 via Bayes' rule. Hearing a weaker
expression triggers a scalar implicature: the listener infers the speaker
*chose not* to use a stronger expression, shifting probability away from
worlds where the stronger expression would have been true. -/

/-- **L1 hearing "caused"**: higher probability for full-causation world
than no-causation world.

L1("caused") assigns positive mass only to worlds where "caused" is
literally true (H ∧ (W ∨ S)). The no-causation world (F,F,F) gets zero. -/
theorem l1_cfg_caused_identifies_full :
    cfg.L1 .caused scenario1 > cfg.L1 .caused scenario4 := by
  rsa_predict

/-- **L1 scalar implicature for "enabled"**: hearing "enabled" makes the
listener prefer worlds where "caused" is *false* over worlds where it's true.

Both (T,F,F) and (T,T,T) make "enabled" literally true (W ∨ S). But at
(T,T,T), S1 would have said "caused" instead (more informative), so
L1 down-weights (T,T,T) upon hearing "enabled." This is the classic
scalar implicature: "enabled" ⇝ ¬caused. -/
theorem l1_cfg_enabled_implicature :
    cfg.L1 .enabled ⟨true, false, false⟩ > cfg.L1 .enabled scenario1 := by
  rsa_predict

/-- **L1 hearing "madeNoDifference"**: identifies the no-causation world.

"madeNoDifference" is true only at (F,F,F), so L1 assigns it probability 1. -/
theorem l1_cfg_noDiff_identifies_none :
    cfg.L1 .madeNoDifference scenario4 > cfg.L1 .madeNoDifference scenario1 := by
  rsa_predict


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

/-! ## Bridge to Core.Causal

Beller & Gerstenberg's W, H, S dimensions can be COMPUTED from structural
causal models, grounding the primitive Boolean features in the counterfactual
reasoning machinery of `Core.Causal`.

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

open Core.Causal

/-- Compute a `CausalWorld` from a structural causal model. -/
def causalWorldFromModel (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : CausalWorld :=
  { whether := decide (causallyNecessary dyn bg cause effect)
  , how := decide (hasDirectLaw dyn cause effect)
  , sufficient := decide (causallySufficient dyn bg cause effect) }

private def mA : Variable := mkVar "bg_cause"
private def mB : Variable := mkVar "bg_alt"
private def mC : Variable := mkVar "bg_effect"
private def mI : Variable := mkVar "bg_intermediate"

/-- Solo cause model: one direct law, a → c. -/
private def soloModel : CausalDynamics := ⟨[CausalLaw.simple mA mC]⟩

/-- Overdetermination model: a ∨ b → c, with b active in background. -/
private def overdetModel : CausalDynamics :=
  CausalDynamics.disjunctiveCausation mA mB mC
private def overdetBg : Situation := Situation.empty.extend mB true

/-- Causal chain model: a → intermediate → c. -/
private def chainModel : CausalDynamics :=
  CausalDynamics.causalChain mA mI mC

/-- Solo cause → full causation world (W=1, H=1, S=1).
When there's one direct cause and no alternatives, all three
causal dimensions are active. -/
theorem solo_cause_world :
    causalWorldFromModel soloModel Situation.empty mA mC =
    ⟨true, true, true⟩ := by native_decide

/-- Overdetermination → W=false, H=true, S=true.
The cause is sufficient (S) and directly connected (H), but NOT
necessary (W=false) because the alternative cause in the background
would produce the effect anyway. -/
theorem overdetermination_world :
    causalWorldFromModel overdetModel overdetBg mA mC =
    ⟨false, true, true⟩ := by native_decide

/-- Causal chain → W=false, H=false, S=true.
Under @cite{nadathur-2024} Def 10b, the initial cause is sufficient (S)
but NOT necessary (W=false): the intermediate can be set directly,
bypassing the root cause. This is correct for Def 10b's domain
(prerequisite semantics), though it diverges from simpler but-for tests
for chain causation. -/
theorem chain_world :
    causalWorldFromModel chainModel Situation.empty mA mC =
    ⟨false, false, true⟩ := by native_decide

-- Expression predictions from structural models

/-- Solo cause: "caused" is literally true. -/
theorem solo_cause_expression_caused :
    expressionMeaning (causalWorldFromModel soloModel Situation.empty mA mC)
      .caused = true := by native_decide

/-- Chain causation: "caused" is NOT literally true (H=false).
Despite sufficiency and necessity, the lack of direct connection
means "caused" doesn't apply. Speakers would use "enabled" instead. -/
theorem chain_not_caused :
    expressionMeaning (causalWorldFromModel chainModel Situation.empty mA mC)
      .caused = false := by native_decide

/-- Chain causation: "enabled" still applies (W ∨ S = true). -/
theorem chain_still_enabled :
    expressionMeaning (causalWorldFromModel chainModel Situation.empty mA mC)
      .enabled = true := by native_decide

/-- Overdetermination: "caused" is literally true (H ∧ S). -/
theorem overdetermination_caused :
    expressionMeaning (causalWorldFromModel overdetModel overdetBg mA mC)
      .caused = true := by native_decide

/-- Bridge between B&G's "caused" and @cite{nadathur-lauer-2020}'s make/cause.

In overdetermination, N&L's `makeSem` holds (sufficient) but `causeSem`
fails (not necessary). B&G's "caused" applies (H ∧ S = true). The
divergence reflects different questions: N&L model *verb choice*
(make vs cause), B&G model *expression choice* (caused vs enabled). -/
theorem bg_caused_vs_nl_cause_diverge :
    expressionMeaning (causalWorldFromModel overdetModel overdetBg mA mC) .caused = true ∧
    causallySufficient overdetModel overdetBg mA mC ∧
    ¬ (causallyNecessary overdetModel overdetBg mA mC) := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

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

1. **Structural**: A `CausalDynamics` (structural equation model) yields
   directness and necessity via `hasDirectLaw` / `causallyNecessary`
2. **Causation type**: These determine production vs dependence
   causation via `causationType` (from `ProductionDependence.lean`)
3. **Semantic + Pragmatic**: The derived `CausalWorld` determines which
   expressions are literally true, and the S1 pragmatic speaker selects
   the most informative one

These are the deepest integration points: a change to `normalDevelopment`,
`expressionMeaning`, or the L0/S1 computation would break these theorems. -/

section EndToEnd

open Core.Causal
open Semantics.Causation.ProductionDependence (causationType)

/-- **Solo cause → P-CAUSE → S1 prefers "caused".**

From a structural model with one direct law (a → c), the full pipeline
produces the correct pragmatic prediction: the S1 speaker selects
"caused" over "enabled" and "affected." -/
theorem solo_cause_chain :
    let cw := causalWorldFromModel soloModel Situation.empty mA mC
    causationType
        (decide (causallyNecessary soloModel Situation.empty mA mC))
        (decide (hasDirectLaw soloModel mA mC)) = some .production ∧
    expressionMeaning cw .caused = true ∧
    cfg.S1 () cw .caused > cfg.S1 () cw .enabled ∧
    cfg.S1 () cw .caused > cfg.S1 () cw .affected := by
  refine ⟨by native_decide, by native_decide, ?_, ?_⟩
  -- cw reduces to ⟨true, true, true⟩ = scenario1
  · have h : causalWorldFromModel soloModel Situation.empty mA mC = scenario1 := by
      native_decide
    rw [h]; exact s1_cfg_full_caused_gt_enabled
  · have h : causalWorldFromModel soloModel Situation.empty mA mC = scenario1 := by
      native_decide
    rw [h]; exact lt_trans s1_cfg_full_enabled_gt_affected s1_cfg_full_caused_gt_enabled

/-- **Causal chain → S1 prefers "enabled".**

From a causal chain (a → intermediate → c), direct interaction is absent
(H=false): the cause operates through an intermediate. "caused" is
literally FALSE, so the S1 speaker selects "enabled" instead.
Under @cite{nadathur-2024} Def 10b, the chain root is also NOT necessary
(W=false) because the intermediate can be set directly. The causation type
becomes `none` (neither production nor dependence). -/
theorem chain_cause_chain :
    let cw := causalWorldFromModel chainModel Situation.empty mA mC
    causationType
        (decide (causallyNecessary chainModel Situation.empty mA mC))
        (decide (hasDirectLaw chainModel mA mC)) = none ∧
    expressionMeaning cw .caused = false ∧
    expressionMeaning cw .enabled = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- **Overdetermination: B&G's "caused" diverges from N&L's `causeSem`.**

With disjunctive causation (a ∨ b → c, both present), the cause is
direct and sufficient but NOT necessary. B&G's "caused" applies
(H ∧ S = true) while @cite{nadathur-lauer-2020}'s `causeSem` returns
false (necessity fails). This is a genuine theoretical divergence:
B&G model *expression choice* (how speakers describe events),
N&L model *verb argument structure* (make vs cause). -/
theorem overdetermination_divergence :
    let cw := causalWorldFromModel overdetModel overdetBg mA mC
    causationType
        (decide (causallyNecessary overdetModel overdetBg mA mC))
        (decide (hasDirectLaw overdetModel mA mC)) = some .production ∧
    expressionMeaning cw .caused = true ∧
    ¬ Semantics.Causation.Necessity.causeSem overdetModel overdetBg mA mC := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

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
