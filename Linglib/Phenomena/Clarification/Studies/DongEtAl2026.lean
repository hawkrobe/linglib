import Linglib.Phenomena.Clarification.Basic
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Dong, Hu, Hui, Zhang, Vulić, Bobu & Collier (2026)
@cite{dong-etal-2026}

Value of Information: A Framework for Human–Agent Communication.

## Overview

LLM agents face a clarify-or-commit dilemma: ask the user for clarification
(incurring cognitive cost) or act on incomplete information (risking error).
This paper proposes a **Value of Information** (VoI) framework: agents ask
question q only when VoI(q) exceeds communication cost c.

## Key Definitions

- `VoI(q) = V_post(b, q) − V(b)`: expected utility improvement from asking q
- `NetVoI(q) = VoI(q) − c`: net value after communication cost
- Policy: ask `q* = argmax_q NetVoI(q)` if `NetVoI(q*) > 0`, else commit

## Connection to linglib infrastructure

- VoI(q) for a partition-based question IS `questionUtility` from
  `Core.Agent.DecisionTheory` (@cite{van-rooy-2003})
- VoI(q) for a stochastic observation IS `eig` from
  `Core.Agent.ExperimentDesign` (@cite{lindley-1956})
- EVPI (from `Phenomena.Clarification.Basic`) upper-bounds VoI(q) for any q,
  since the identity partition is the finest (@cite{raiffa-schlaifer-1961})

## Risk-Sensitivity

The key empirical finding (Figure 4): agents ask more questions in
high-stakes tasks (medical diagnosis, U = 10) than low-stakes (animal
guessing, U = 1), even at identical uncertainty. This follows from
EVPI scaling linearly with utility magnitude.

## Formalization

- §1–4: Decision-theoretic layer (VoI, EVPI, scaling). ℚ-valued
  `DecisionProblem` with `native_decide` proofs.
- §5: RSA identification model. ℝ-valued `RSAConfig` with `rsa_predict`
  proofs. The RSA behavioral predictions are IDENTICAL regardless of
  reward magnitude k: meaning is Boolean (correct or not), so the response
  distribution doesn't depend on stakes. Risk-sensitivity is captured
  only by EVPI, not by the behavioral policy.
-/

namespace Phenomena.Clarification.Studies.DongEtAl2026

open Core.DecisionTheory Phenomena.Clarification BigOperators Finset

-- ============================================================================
-- §1. Net Value of Information
-- ============================================================================

/-- Net value of information for a partition-based question q.
    `NetVoI(q) = questionUtility(q) − c`.
    The agent asks q when `NetVoI(q) > 0`. -/
def netVoI {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q : Question W) (c : ℚ) : ℚ :=
  questionUtility dp actions q - c

/-- EVPI upper-bounds VoI for any question: since the identity partition
    is the finest, `questionUtility q ≤ EVPI` for all q.

    This follows from `questionUtility_ge_of_refines` in `Core.Partition`:
    finer partitions have higher question utility, and the identity
    partition is maximally fine.

    TODO: construct the identity partition for arbitrary `Fintype W`
    and apply `questionUtility_ge_of_refines`. -/
theorem netVoI_le_evpi {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A)
    (q : Question W) (c : ℚ) :
    netVoI dp actions q c ≤ evpi dp actions - c := by
  sorry

-- ============================================================================
-- §2. Risk-Sensitivity via Utility Scaling
-- ============================================================================

/-- Scale all utilities in a decision problem by factor k.
    Models the difference between high-stakes (k = 10, medical diagnosis)
    and low-stakes (k = 1, animal guessing) tasks. -/
def scaleUtility {W A : Type*} (dp : DecisionProblem W A) (k : ℚ) :
    DecisionProblem W A where
  utility w a := k * dp.utility w a
  prior := dp.prior

/-- Expected utility scales linearly with utility magnitude.

    TODO: after `simp_rw` with `ring`, the goal reduces to
    `∑ x, k * (dp.prior x * dp.utility x a) = k * ∑ w, ...`,
    which is `Finset.mul_sum` — not transitively imported. -/
theorem expectedUtility_scale {W A : Type*} [Fintype W] [DecidableEq W]
    (dp : DecisionProblem W A) (a : A) (k : ℚ) :
    expectedUtility (scaleUtility dp k) a = k * expectedUtility dp a := by
  sorry

/-- **Risk-sensitivity**: EVPI scales linearly with utility magnitude.

    High-stakes tasks (k large) have proportionally higher EVPI, so
    `NetVoI = EVPI − c` stays positive for more questions before the
    fixed cost c dominates. This is the mechanism behind Figure 4:
    at identical confidence, VoI is higher for medical diagnosis (U = 10)
    than animal guessing (U = 1).

    TODO: prove `oracleValue` and `dpValue` each scale by k (requires
    showing `max` distributes over non-negative scaling). -/
theorem evpi_scale {W A : Type*} [Fintype W] [DecidableEq W] [DecidableEq A]
    (dp : DecisionProblem W A) (actions : List A) (k : ℚ) (_hk : 0 ≤ k) :
    evpi (scaleUtility dp k) actions = k * evpi dp actions := by
  sorry

-- ============================================================================
-- §3. Concrete Example: Animal vs. Medical
-- ============================================================================

/-- Binary identification task (simplified Mixed 20Q). -/
inductive Target where | t₁ | t₂
  deriving DecidableEq, Repr

instance : Fintype Target where
  elems := {.t₁, .t₂}
  complete x := by cases x <;> simp

/-- Binary identification DP: reward k for correct guess, 0 otherwise.
    Uniform prior over 2 targets. -/
def identificationDP (k : ℚ) : DecisionProblem Target Target where
  utility w a := if a == w then k else 0
  prior _ := 1/2

def allTargets : List Target := [.t₁, .t₂]

/-- Identity partition for the binary task. -/
def identityQ : Question Target := [λ t => t == .t₁, λ t => t == .t₂]

/-- Animal guessing (k = 1): EVPI = 1/2.
    Uniform prior, best blind guess has EU = 1/2, perfect info gives 1. -/
theorem evpi_animal :
    evpi (identificationDP 1) allTargets = 1/2 := by native_decide

/-- Medical diagnosis (k = 10): EVPI = 5.
    Same uncertainty, 10× stakes → 10× EVPI. -/
theorem evpi_medical :
    evpi (identificationDP 10) allTargets = 5 := by native_decide

/-- Risk-sensitivity: medical EVPI is strictly greater than animal EVPI. -/
theorem medical_gt_animal :
    evpi (identificationDP 10) allTargets >
    evpi (identificationDP 1) allTargets := by
  native_decide

/-- With communication cost c = 1, the animal-guessing agent should commit
    (EVPI = 1/2 < 1) but the medical-diagnosis agent should clarify
    (EVPI = 5 > 1). This replicates the qualitative pattern in Figure 4. -/
theorem animal_commits :
    netVoI (identificationDP 1) allTargets identityQ 1 ≤ 0 := by
  native_decide

theorem medical_clarifies :
    netVoI (identificationDP 10) allTargets identityQ 1 > 0 := by
  native_decide

-- ============================================================================
-- §4. Scaling Verified Concretely
-- ============================================================================

/-- Concrete verification of linear scaling: EVPI at k = 10 is exactly
    10× EVPI at k = 1, confirming `evpi_scale` for this instance. -/
theorem scaling_concrete :
    evpi (identificationDP 10) allTargets =
    10 * evpi (identificationDP 1) allTargets := by
  native_decide

-- ============================================================================
-- §5. RSA Identification Model
-- ============================================================================

/-! The identification task (Mixed 20Q) maps to an RSA reference game:
utterances are guesses, worlds are true targets. S1 prefers correct guesses
(L0 = 1) over incorrect (L0 = 0). L1 hearing a guess infers the target.

The RSA behavioral predictions are IDENTICAL regardless of reward magnitude k.
Meaning is Boolean (correct or not), so L0/S1/L1 don't depend on stakes.
Risk-sensitivity is captured only by EVPI (§1–4), not by the response
distribution. This mirrors the paper's insight: VoI governs WHETHER to
clarify; the behavioral policy governs WHAT to say when committing. -/

/-- Boolean match: does guess match target? -/
def targetMatches : Target → Target → Bool
  | .t₁, .t₁ => true
  | .t₂, .t₂ => true
  | _, _ => false

open RSA Real in
/-- Binary identification as RSA reference game.
    L0(target|guess) = 1 if correct, 0 if wrong.
    S1(guess|target) ∝ L0(target|guess)^α = 1 if correct, 0 if wrong.
    L1(target|guess) ∝ P(target) · S1(guess|target). -/
noncomputable def identCfg : RSAConfig Target Target where
  meaning _ _ guess target := if targetMatches guess target then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u :=
    if l0 u w = 0 then 0
    else exp (α * log (l0 u w))
  s1Score_nonneg l0 α _ _ u _ _ := by
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

/-- S1 prefers correct guess: S1(t₁|t₁) > S1(t₂|t₁).
    L0(t₁|guess=t₁) = 1, L0(t₁|guess=t₂) = 0. -/
theorem S1_prefers_correct :
    identCfg.S1 () .t₁ .t₁ > identCfg.S1 () .t₁ .t₂ := by
  rsa_predict

/-- L1 correctly infers target from guess: L1(t₁|guess=t₁) > L1(t₂|guess=t₁).
    Since S1(t₁|t₂) = 0 (wrong guess never produced), L1(t₁|guess=t₁) = 1. -/
theorem L1_identifies_correctly :
    identCfg.L1 .t₁ .t₁ > identCfg.L1 .t₁ .t₂ := by
  rsa_predict

/-- The RSA model is symmetric: S1(t₂|t₂) > S1(t₁|t₂). -/
theorem S1_symmetric :
    identCfg.S1 () .t₂ .t₂ > identCfg.S1 () .t₂ .t₁ := by
  rsa_predict

end Phenomena.Clarification.Studies.DongEtAl2026
