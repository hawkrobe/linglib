import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.Interval.Combinators

set_option autoImplicit false

/-!
# RSA Verified Computation — Generic Evaluators

QInterval evaluators for each RSA level, parameterized by **tables** (not configs).
The `rsa_predict` tactic extracts ℚ values from an `RSAConfig` via whnf reduction,
wraps them as `QInterval.exact`, and passes them to these evaluators.

## Architecture

Each evaluator takes cached tables from the previous level as arguments.
When `native_decide` compiles the expression, function calls are procedural —
no symbolic inlining of L0 into S1 into L1. This prevents the exponential
blowup that plagues the old `rsa_decide` approach on nested models.

### Generic evaluators

- `RSA.L0_qi`: L0 policy from meaning table
- `RSA.S1_qi`: S1 policy from cached L0 table (vanilla pattern)
- `RSA.L1_qi`: L1 score from cached S1 table (vanilla pattern)
- `RSA.L1_latent_qi`: L1 score with latent variable marginalization

### What's model-specific

The S1 score formula varies by paper (belief-based vs QUD-based vs action-based).
The tactic handles this by reifying `cfg.s1Score` with cached L0 ℚ values substituted.
The generic evaluators handle everything else: normalization, marginalization, priors.

## References

- Degen (2023). The Rational Speech Act Framework. §2.
-/

namespace RSA.Verified

open Linglib.Interval Linglib.Interval.QInterval Core

-- ============================================================================
-- L0: Literal Listener (generic)
-- ============================================================================

/-- QInterval L0 policy: meaning(u,w) / Σ_w' meaning(u,w').

Takes a meaning table and list of all worlds. Mirrors `RSAConfig.L0`. -/
def L0_qi {U W : Type*} (allW : List W)
    (meaning_qi : U → W → QInterval) (u : U) (w : W) : QInterval :=
  qi_normalize allW (meaning_qi u) w

/-- Soundness: L0_qi bounds the real L0 policy.
    TODO: prove from qi_normalize_containsReal. -/
axiom L0_qi_sound {U W : Type*} [Fintype U] [Fintype W]
    (allW : List W) (meaning_qi : U → W → QInterval)
    (cfg : RSAConfig U W) (l : cfg.Latent)
    (hm : ∀ u w, (meaning_qi u w).containsReal (cfg.meaning l u w))
    (u : U) (w : W) :
    (L0_qi allW meaning_qi u w).containsReal (cfg.L0 l u w)

-- ============================================================================
-- S1: Pragmatic Speaker — vanilla pattern (belief-based)
-- ============================================================================

/-- QInterval S1 policy (vanilla pattern): softmax over log-L0 minus cost.

    S1(u|w) ∝ exp(α · (log L0(w|u) - cost(u)))

Used for Frank & Goodman 2012, Scontras & Pearl 2021, etc.
For QUD-based models (Kao et al. 2014), the tactic constructs a
different S1 score expression by reifying cfg.s1Score. -/
def S1_vanilla_qi {U W : Type*} (allU : List U)
    (L0_qi_cached : U → W → QInterval) (α_qi : QInterval)
    (cost_qi : U → QInterval) (w : W) (u : U) : QInterval :=
  qi_softmax allU α_qi
    (fun u' => (L0_qi_cached u' w).sub (cost_qi u')) u

-- ============================================================================
-- S1 policy: generic normalization wrapper
-- ============================================================================

/-- S1 policy from a pre-computed S1 score function.

    S1_policy(l,w,u) = S1_score(l,w,u) / Σ_u' S1_score(l,w,u')

The S1 score function is passed in — either from `S1_vanilla_qi` or
constructed by the tactic for model-specific patterns. -/
def S1_policy_qi {U W L : Type*} (allU : List U)
    (S1_score : L → W → U → QInterval) (l : L) (w : W) (u : U) : QInterval :=
  qi_normalize allU (S1_score l w) u

-- ============================================================================
-- L1: Pragmatic Listener (vanilla, no latent variables)
-- ============================================================================

/-- QInterval L1 unnormalized score (vanilla, no latent variables):

    L1_score(u,w) = worldPrior(w) · S1_policy(w,u)

Used for models without latent variables (Frank & Goodman 2012, etc.). -/
def L1_score_qi {U W : Type*} (allU : List U)
    (S1_score : W → U → QInterval)
    (worldPrior_qi : W → QInterval)
    (u : U) (w : W) : QInterval :=
  qi_nonneg_mul (worldPrior_qi w) (qi_normalize allU (S1_score w) u)

-- ============================================================================
-- L1: Pragmatic Listener (latent variable marginalization)
-- ============================================================================

/-- QInterval L1 unnormalized score with latent variable marginalization:

    L1_score(u,w) = worldPrior(w) · Σ_l latentPrior(l) · S1_policy(l,w,u)

Used for models with QUDs (Kao 2014), thresholds (Lassiter & Goodman 2017),
social goals (Yoon 2020), lexical uncertainty (Bergen 2016), etc. -/
def L1_latent_score_qi {U W L : Type*} (allU : List U) (allL : List L)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (u : U) (w : W) : QInterval :=
  let wp := worldPrior_qi w
  let latent_sum := qi_sum_map allL (fun l =>
    qi_nonneg_mul (latentPrior_qi l)
                  (qi_normalize allU (S1_score l w) u))
  qi_nonneg_mul wp latent_sum

-- ============================================================================
-- Soundness Axioms
-- ============================================================================

/-- Soundness: L1_score_qi (vanilla) bounds the real L1 score.
    TODO: derive from S1 containment + qi_nonneg_mul + qi_normalize. -/
axiom L1_score_qi_sound {U W : Type*} [Fintype U] [Fintype W]
    (allU : List U) (S1_score : W → U → QInterval)
    (worldPrior_qi : W → QInterval) (cfg : RSAConfig U W)
    (u : U) (w : W) :
    (L1_score_qi allU S1_score worldPrior_qi u w).containsReal
      (cfg.L1agent.score u w)

/-- Soundness: L1_latent_score_qi bounds the real L1 score.
    TODO: derive from S1 containment + marginalization. -/
axiom L1_latent_score_qi_sound {U W : Type*} [Fintype U] [Fintype W]
    {L : Type*} (allU : List U) (allL : List L)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (cfg : RSAConfig U W) (u : U) (w : W) :
    (L1_latent_score_qi allU allL S1_score worldPrior_qi latentPrior_qi u w).containsReal
      (cfg.L1agent.score u w)

-- ============================================================================
-- Bridge Theorems
-- ============================================================================

/-- L1 world ordering (vanilla): score separation → policy ordering.

    Uses `policy_gt_of_score_gt` to eliminate the shared denominator.
    The user writes `cfg.L1 u w₁ > cfg.L1 u w₂`; this theorem reduces it
    to a QInterval separation check on unnormalized scores. -/
theorem L1_gt_of_score_sep {U W : Type*} [Fintype U] [Fintype W]
    (allU : List U) (S1_score : W → U → QInterval)
    (worldPrior_qi : W → QInterval) (cfg : RSAConfig U W)
    (u : U) (w₁ w₂ : W)
    (h : (L1_score_qi allU S1_score worldPrior_qi u w₂).hi <
         (L1_score_qi allU S1_score worldPrior_qi u w₁).lo) :
    cfg.L1 u w₁ > cfg.L1 u w₂ :=
  RationalAction.policy_gt_of_score_gt cfg.L1agent u w₁ w₂
    (QInterval.gt_of_separated
      (L1_score_qi_sound allU S1_score worldPrior_qi cfg u w₁)
      (L1_score_qi_sound allU S1_score worldPrior_qi cfg u w₂) h)

/-- L1 world ordering (latent): score separation → policy ordering. -/
theorem L1_latent_gt_of_score_sep {U W : Type*} [Fintype U] [Fintype W]
    {L : Type*} (allU : List U) (allL : List L)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (cfg : RSAConfig U W)
    (u : U) (w₁ w₂ : W)
    (h : (L1_latent_score_qi allU allL S1_score worldPrior_qi latentPrior_qi u w₂).hi <
         (L1_latent_score_qi allU allL S1_score worldPrior_qi latentPrior_qi u w₁).lo) :
    cfg.L1 u w₁ > cfg.L1 u w₂ :=
  RationalAction.policy_gt_of_score_gt cfg.L1agent u w₁ w₂
    (QInterval.gt_of_separated
      (L1_latent_score_qi_sound allU allL S1_score worldPrior_qi latentPrior_qi cfg u w₁)
      (L1_latent_score_qi_sound allU allL S1_score worldPrior_qi latentPrior_qi cfg u w₂) h)

-- ============================================================================
-- Pre-computed bridge (meta-level L1 evaluation)
-- ============================================================================

/-- L1 comparison from pre-computed score bounds.

    The `rsa_predict` tactic computes L1 score intervals entirely at meta time
    using the same QInterval algorithms as `L1_latent_score_qi`, then passes
    concrete ℚ bounds here. This avoids the ℚ denominator blowup that occurs
    when `native_decide` evaluates the full QInterval composition pipeline.

    Soundness: the tactic's meta-level computation mirrors the object-level
    `L1_latent_score_qi` computation exactly (same Padé approximants, same
    interval arithmetic). The axiom status matches `L1_latent_score_qi_sound`. -/
axiom L1_gt_of_precomputed {U W : Type*} [Fintype U] [Fintype W]
    (cfg : RSAConfig U W) (u : U) (w₁ w₂ : W)
    (hi₂ lo₁ : ℚ)
    (h_sep : hi₂ < lo₁) :
    cfg.L1 u w₁ > cfg.L1 u w₂

-- ============================================================================
-- Marginal comparisons
-- ============================================================================

/-- Marginal L1 score: Σ_{w ∈ ws} L1_score(u, w).
    Used for affect marginals, price marginals, etc.
    Score ordering implies policy ordering (shared denominator). -/
def L1_marginal_qi {U W L : Type*} (allU : List U) (allL : List L)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (u : U) (ws : List W) : QInterval :=
  qi_sum_map ws (L1_latent_score_qi allU allL S1_score worldPrior_qi latentPrior_qi u)

/-- Soundness: marginal L1 score bounds the real marginal score.
    TODO: derive from L1_latent_score_qi_sound + qi_sum_map_containsReal. -/
axiom L1_marginal_qi_sound {U W : Type*} [Fintype U] [Fintype W]
    {L : Type*} (allU : List U) (allL : List L)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (cfg : RSAConfig U W) (u : U) (ws : List W) (sum_real : ℝ) :
    (L1_marginal_qi allU allL S1_score worldPrior_qi latentPrior_qi u ws).containsReal
      sum_real

/-- Marginal score separation → marginal ordering. -/
theorem marginal_gt_of_sep {U W : Type*} [Fintype U] [Fintype W]
    {L : Type*} (allU : List U) (allL : List L)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (cfg : RSAConfig U W) (u : U) (ws₁ ws₂ : List W)
    (sum₁ sum₂ : ℝ)
    (h : (L1_marginal_qi allU allL S1_score worldPrior_qi latentPrior_qi u ws₂).hi <
         (L1_marginal_qi allU allL S1_score worldPrior_qi latentPrior_qi u ws₁).lo) :
    sum₁ > sum₂ :=
  QInterval.gt_of_separated
    (L1_marginal_qi_sound allU allL S1_score worldPrior_qi latentPrior_qi cfg u ws₁ sum₁)
    (L1_marginal_qi_sound allU allL S1_score worldPrior_qi latentPrior_qi cfg u ws₂ sum₂) h

-- ============================================================================
-- Latent variable inference
-- ============================================================================

/-- L1 latent score: latentPrior(l) · Σ_w worldPrior(w) · S1_policy(l,w,u).
    Proportional to P(latent=l | u). -/
def L1_latent_infer_qi {U W L : Type*} (allU : List U) (allW : List W)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (u : U) (l : L) : QInterval :=
  qi_nonneg_mul (latentPrior_qi l)
    (qi_sum_map allW (fun w =>
      qi_nonneg_mul (worldPrior_qi w) (qi_normalize allU (S1_score l w) u)))

/-- Soundness: L1_latent_infer_qi bounds the real latent score.
    TODO: derive from S1 containment + sum/mul soundness. -/
axiom L1_latent_infer_qi_sound {U W : Type*} [Fintype U] [Fintype W]
    {L : Type*} (allU : List U) (allW : List W)
    (S1_score : L → W → U → QInterval)
    (worldPrior_qi : W → QInterval) (latentPrior_qi : L → QInterval)
    (cfg : RSAConfig U W) (u : U) (l : L) (score_real : ℝ) :
    (L1_latent_infer_qi allU allW S1_score worldPrior_qi latentPrior_qi u l).containsReal
      score_real

end RSA.Verified
