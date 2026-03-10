import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.Agent.ChoiceApproximations

/-!
# Speaker Discrimination: JND/Trace on S1
@cite{degen-2023} @cite{luce-1959}

Applies the just-noticeable-difference (JND) and trace infrastructure from
@cite{luce-1959} — formalized in `ChoiceApproximations.lean` — to S1's
utterance choice in RSA.

## Key idea

S1 is a `RationalAction W U`: given world `w` and latent `l`, S1 assigns
each utterance `u` a score, which determines a Luce choice rule. The
score function `S1agent.score w : U → ℝ` is therefore a ratio scale on
utterances, and the JND/trace machinery applies directly:

- **S1_jndL**: utterance `u₁` is discriminably preferred over `u₂` at
  threshold `π` — the speaker reliably chooses `u₁` over `u₂`
- **S1_jndI**: utterances `u₁` and `u₂` are pragmatically indistinguishable
  — the speaker cannot reliably discriminate between them
- **S1_traceGe**: the trace ordering on utterances, which recovers the
  latent preference ranking

## Strict positivity

The JND/trace theorems in `ChoiceApproximations.lean` require **strictly
positive** scale values (`0 < v a`), matching Luce's assumption that every
alternative has positive value. This is stronger than `score_nonneg` (`0 ≤`).
The positivity hypothesis `hv_pos` is carried explicitly — it holds whenever
S1's score function is strictly positive (e.g., for exponential scoring rules
like `exp(α · u)`, but not necessarily for `rpow(L0, α)` when some L0 values
are zero).

## Properties (zero sorry in §3)

All semiorder and trace properties follow by direct application of the
corresponding theorems in `ChoiceApproximations.lean`:
- L-transitivity, I-symmetry, I-reflexivity
- Trace ↔ score ordering

## L1 invariance (sorry'd)

If S1 scores match everywhere for two utterances, L1 posteriors are
identical. This is stated but sorry'd — the proof requires showing that
equal S1 policies yield equal L1agent scores.

-/

namespace RSA

open Core BigOperators

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U]

namespace RSAConfig

-- ============================================================================
-- §1. S1 as a ratio scale
-- ============================================================================

/-- S1's score function viewed as a ratio scale on utterances.

Given a latent value `l` and world `w`, this is the function `U → ℝ`
that the JND/trace machinery operates on. -/
noncomputable def S1_scale (cfg : RSAConfig U W) (l : cfg.Latent) (w : W) : U → ℝ :=
  (cfg.S1agent l).score w

-- ============================================================================
-- §2. S1 JND relations
-- ============================================================================

/-- S1-discriminable preference: utterance `u₁` is discriminably preferred
over `u₂` by the pragmatic speaker at threshold `thr`.

This means S1 reliably chooses `u₁` over `u₂` in a binary forced choice:
`P(u₁, {u₁, u₂}) > thr`. -/
def S1_jndL (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (thr : ℝ) (u₁ u₂ : U) : Prop :=
  jndL (cfg.S1_scale l w) thr u₁ u₂

/-- S1-indistinguishable utterances: the pragmatic speaker cannot reliably
discriminate between `u₁` and `u₂` at threshold `thr`.

This defines a pragmatic tolerance band: utterances within it are
interchangeable from S1's perspective. -/
def S1_jndI (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (thr : ℝ) (u₁ u₂ : U) : Prop :=
  jndI (cfg.S1_scale l w) thr u₁ u₂

/-- S1 trace ordering on utterances: `u₁ ≥_T u₂` iff
`P(u₁, z) ≥ P(u₂, z)` for all utterances `z`. -/
def S1_traceGe (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (u₁ u₂ : U) : Prop :=
  traceGe (cfg.S1_scale l w) u₁ u₂

-- ============================================================================
-- §3. Properties from ChoiceApproximations
-- ============================================================================

/-- L-transitivity for S1 preferences: if S1 discriminably prefers `u₁`
over `u₂` and `u₂` over `u₃`, then S1 discriminably prefers `u₁` over `u₃`.

Requires strict positivity of S1 scores (Luce's ratio scale assumption). -/
theorem S1_jndL_trans (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (hv_pos : ∀ u, 0 < cfg.S1_scale l w u)
    (thr : ℝ) (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1)
    (u₁ u₂ u₃ : U)
    (h₁₂ : cfg.S1_jndL l w thr u₁ u₂) (h₂₃ : cfg.S1_jndL l w thr u₂ u₃) :
    cfg.S1_jndL l w thr u₁ u₃ :=
  jndL_trans (cfg.S1_scale l w) hv_pos thr hthr_lower hthr_upper u₁ u₂ u₃ h₁₂ h₂₃

/-- I-symmetry for S1 indistinguishability: if `u₁` and `u₂` are
indistinguishable, so are `u₂` and `u₁`. -/
theorem S1_jndI_symm (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (hv_pos : ∀ u, 0 < cfg.S1_scale l w u)
    (thr : ℝ) (u₁ u₂ : U)
    (h : cfg.S1_jndI l w thr u₁ u₂) :
    cfg.S1_jndI l w thr u₂ u₁ :=
  jndI_symm (cfg.S1_scale l w) hv_pos thr u₁ u₂ h

/-- I-reflexivity for S1: every utterance is indistinguishable from itself. -/
theorem S1_jndI_refl (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (hv_pos : ∀ u, 0 < cfg.S1_scale l w u)
    (thr : ℝ) (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (u : U) :
    cfg.S1_jndI l w thr u u :=
  jndI_refl (cfg.S1_scale l w) hv_pos thr hthr_lower hthr_upper u

/-- Trace ↔ score ordering: `u₁ ≥_T u₂` iff `S1.score(w, u₂) ≤ S1.score(w, u₁)`. -/
theorem S1_trace_iff_score_ge (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (hv_pos : ∀ u, 0 < cfg.S1_scale l w u)
    (u₁ u₂ : U) :
    cfg.S1_traceGe l w u₁ u₂ ↔ (cfg.S1agent l).score w u₂ ≤ (cfg.S1agent l).score w u₁ :=
  trace_iff_scale_ge (cfg.S1_scale l w) hv_pos u₁ u₂

-- ============================================================================
-- §4. L1 invariance under S1-equivalent utterances
-- ============================================================================

omit [DecidableEq U] in
/-- If S1 scores match everywhere for two utterances, L1 posteriors are identical.

When `S1agent.score w u₁ = S1agent.score w u₂` for all latent values and
worlds, the two utterances are indistinguishable at L1: the pragmatic
listener assigns them the same posterior over worlds. -/
theorem L1_eq_of_S1_score_eq (cfg : RSAConfig U W) (u₁ u₂ : U)
    (h_eq : ∀ (l : cfg.Latent) (w : W),
      (cfg.S1agent l).score w u₁ = (cfg.S1agent l).score w u₂)
    (w : W) : cfg.L1 u₁ w = cfg.L1 u₂ w := by
  -- S1 scores match → S1 policies match (totalScore is the same denominator)
  have h_S1 : ∀ l w, cfg.S1 l w u₁ = cfg.S1 l w u₂ := fun l w =>
    RationalAction.policy_eq_of_score_eq _ w u₁ u₂ (h_eq l w)
  -- L1 scores match (worldPrior and latentPrior are u-independent)
  have h_score : ∀ w, cfg.L1agent.score u₁ w = cfg.L1agent.score u₂ w := fun w' => by
    show cfg.worldPrior w' * ∑ l, cfg.latentPrior w' l * cfg.S1 l w' u₁ =
         cfg.worldPrior w' * ∑ l, cfg.latentPrior w' l * cfg.S1 l w' u₂
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [h_S1 l w']
  -- L1 totalScores match (sum of equal scores)
  have h_total : cfg.L1agent.totalScore u₁ = cfg.L1agent.totalScore u₂ :=
    Finset.sum_congr rfl fun w' _ => h_score w'
  -- policy = score / totalScore, both numerator and denominator equal
  simp only [L1, RationalAction.policy, h_score w, h_total]

end RSAConfig

end RSA
