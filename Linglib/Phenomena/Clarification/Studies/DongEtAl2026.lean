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

## RSA framing

The paper explicitly adopts an RSA perspective (@cite{frank-goodman-2012};
@cite{goodman-frank-2016}), viewing dialogue as rational action. VoI(q)
(eq. 4: V_post(b,q) − V(b)) is structurally the same as `questionUtility`
(@cite{van-rooy-2003}): the expected gain in decision value from asking q.

## Connection to @cite{hawkins-etal-2025}

VoI captures WHETHER to ask (the questioner's decision), while the commit
action (argmax over expected utility) captures WHAT to do. The VoI
framework is complementary to @cite{hawkins-etal-2025}'s respondent model.

## Risk-Sensitivity and Action Utility

The key qualitative finding (Appendix A, Figure 4): in the Mixed 20Q task,
the VoI agent asks more questions for medical diagnosis (U = 10) than
animal guessing (U = 1), because higher stakes increase expected regret.

Action-utility scoring (@cite{hawkins-etal-2025}'s β > 0) encodes stakes
into s1Score: `exp(α · U(target, guess))` scales with reward k. In richer
models (multiple targets with partial matches), this creates δ-sensitive
S1 preferences — the mechanism behind the @cite{tsvilodub-etal-2026}
formalization's cross-config comparisons.

In this binary identification task, however, the action-utility effect is
degenerate: the L0 gate zeros the wrong guess, so S1 assigns probability 1
to the correct guess regardless of k. The task is too simple for action
utility to produce qualitative differences — both k = 1 and k = 10 yield
identical S1/L1 predictions after normalization.
-/

namespace Phenomena.Clarification.Studies.DongEtAl2026

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- Binary identification task (simplified from the paper's Mixed-Stakes
    20 Questions, which uses 100 animals / 15 diseases). -/
inductive Target where | t₁ | t₂
  deriving DecidableEq, Repr

instance : Fintype Target where
  elems := {.t₁, .t₂}
  complete x := by cases x <;> simp

-- ============================================================================
-- §2. RSA Identification Model
-- ============================================================================

/-- Boolean match: does guess match target? -/
def targetMatches : Target → Target → Bool
  | .t₁, .t₁ => true
  | .t₂, .t₂ => true
  | _, _ => false

open RSA Real in
/-- Binary identification as RSA reference game with action-utility scoring.

    s1Score(L0, α, target, guess) =
      if L0(target|guess) = 0 then 0
      else exp(α · k)

    At k = 1 and k = 10, S1(correct|target) = 1 after normalization —
    the binary task is degenerate. Action-utility scoring IS the right
    mechanism (@cite{hawkins-etal-2025}'s β = 1), but the task is too
    simple for it to produce qualitative differences. -/
noncomputable def identCfg (k : ℝ) (hk : 0 ≤ k) : RSAConfig Target Target where
  meaning _ _ guess target := if targetMatches guess target then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u :=
    if l0 u w = 0 then 0
    else exp (α * match u, w with
      | .t₁, .t₁ => k
      | .t₂, .t₂ => k
      | _, _      => (0 : ℝ))
  s1Score_nonneg l0 α _ _ u _ _ := by
    show 0 ≤ (if l0 u _ = 0 then (0 : ℝ) else exp _)
    split
    · exact le_refl 0
    · exact le_of_lt (exp_pos _)
  α := 1
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

/-- Animal guessing (k = 1). -/
noncomputable def animalCfg := identCfg 1 (by norm_num)

/-- Medical diagnosis (k = 10). -/
noncomputable def medicalCfg := identCfg 10 (by norm_num)

-- ============================================================================
-- §3. Predictions
-- ============================================================================

/-! Both configs produce identical S1/L1 predictions — the binary task is
degenerate. The L0 gate zeros wrong guesses, so S1 assigns probability 1
to the correct guess at any k. -/

/-- S1 prefers correct guess (animal guessing, k = 1). -/
theorem S1_animal_prefers_correct :
    animalCfg.S1 () .t₁ .t₁ > animalCfg.S1 () .t₁ .t₂ := by
  rsa_predict

/-- S1 prefers correct guess (medical diagnosis, k = 10).
    Same qualitative prediction despite 10× stakes. -/
theorem S1_medical_prefers_correct :
    medicalCfg.S1 () .t₁ .t₁ > medicalCfg.S1 () .t₁ .t₂ := by
  rsa_predict

/-- L1 correctly infers target from guess (animal). -/
theorem L1_animal_identifies :
    animalCfg.L1 .t₁ .t₁ > animalCfg.L1 .t₁ .t₂ := by
  rsa_predict

/-- L1 correctly infers target from guess (medical).
    Same qualitative prediction despite 10× stakes. -/
theorem L1_medical_identifies :
    medicalCfg.L1 .t₁ .t₁ > medicalCfg.L1 .t₁ .t₂ := by
  rsa_predict

end Phenomena.Clarification.Studies.DongEtAl2026
