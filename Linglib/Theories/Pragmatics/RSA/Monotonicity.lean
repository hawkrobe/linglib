import Linglib.Theories.Pragmatics.RSA.Basic

/-!
# RSA Monotonicity — Structural Order-Preserving Lemmas

@cite{frank-goodman-2012} @cite{degen-2023}

Structural lemmas that reduce RSA inequality proofs to qualitative claims about
the underlying scores, costs, and meanings — peeling off one layer of
softmax/Bayes per rewrite. Companion to `Basic.lean`'s
`L1_latent_lt_of_score_lt` and `L1_marginal_lt_of_score_sum_lt`.

The intent is to shrink the footprint of the `rsa_predict` numerical-reflection
tactic: when an inequality holds because of a structural fact (denominator
cancellation, monotonicity of softmax in the score, monotonicity of the
score in `L0` or `cost`), prove it by chaining these lemmas instead of
verifying the resulting ratio numerically.

## Layering

The full softmax stack is:

    L1 u w ∝ worldPrior w · Σ_l latentPrior w l · S1 l w u
    S1 l w u = s1Score(L0(l).policy, α, l, w, u) / Σ_{u'} s1Score(...)
    L0 l u w = meaning(initial, l, u, w) / Σ_{w'} meaning(initial, l, u, w')

Each layer normalizes by a denominator that **cancels** when comparing two
values *at the same conditioning point*:

- `L1 u w₁ vs L1 u w₂`: same `u` → same `L1agent.totalScore u`
- `S1 l w u₁ vs S1 l w u₂`: same `l, w` → same `S1agent.totalScore w`
- `L0 l u w₁ vs L0 l u w₂`: same `l, u` → same `L0agent.totalScore u`

For these comparisons, this file provides `*_lt_of_score_lt` lemmas that
discharge the inequality from a score comparison alone, skipping the heavy
softmax denominator computation that `rsa_predict` would otherwise verify
numerically. All such lemmas are tagged `@[gcongr]`, so user code can write
`by gcongr; rsa_predict` instead of invoking the lemma by name.

## Score-shape lemmas

Once a comparison reduces to scores, the score function's shape determines
the next reduction. For the two canonical `s1Score` patterns:

- **Belief-based** `s1Score = rpow L0 α`:
    `S1score lt ↔ L0 lt` (since `rpow _ α` is strictly monotone for α > 0)
- **Action-based** `s1Score = exp(α · (log L0 - cost))`:
    `S1score lt ↔ α(log L0 - cost) lt` (since `exp` is strictly monotone)

These shape lemmas live below as `S1_belief_score_lt_iff` etc.; they are
parameterized by the scoring rule, so a paper using a custom `s1Score` adds
its own shape lemma instead of invoking `rsa_predict`.
-/

namespace RSA

open Core

variable {U W : Type*} [Fintype U] [Fintype W]

namespace RSAConfig

-- ============================================================================
-- §1. Same-denominator cancellation: L1, S1, L0
-- ============================================================================

/-- L1 cross-world comparison via score comparison.

    Both sides share the same `u`, hence the same `L1agent.totalScore u`,
    which cancels. Reduces a softmax-ratio comparison to a comparison of
    the unnormalized L1 scores.

    Tagged `@[gcongr]` so `gcongr` can peel `cfg.L1 u w₁ < cfg.L1 u w₂` to
    `cfg.L1agent.score u w₁ < cfg.L1agent.score u w₂` automatically.

    Specialization of `RationalAction.policy_lt_of_score_lt` to `L1agent`. -/
@[gcongr]
theorem L1_lt_of_score_lt (cfg : RSAConfig U W) (u : U) (w₁ w₂ : W)
    (h : cfg.L1agent.score u w₁ < cfg.L1agent.score u w₂) :
    cfg.L1 u w₁ < cfg.L1 u w₂ :=
  cfg.L1agent.policy_lt_of_score_lt u w₁ w₂ h

/-- L1 cross-world equality via score equality. -/
theorem L1_eq_of_score_eq (cfg : RSAConfig U W) (u : U) (w₁ w₂ : W)
    (h : cfg.L1agent.score u w₁ = cfg.L1agent.score u w₂) :
    cfg.L1 u w₁ = cfg.L1 u w₂ :=
  cfg.L1agent.policy_eq_of_score_eq u w₁ w₂ h

/-- L1 cross-utterance comparison via cross-product. Different `u` means
    different denominators, so we use the cross-product trick (no positivity
    hypothesis needed — it's derived from the cross-product). -/
@[gcongr]
theorem L1_lt_cross_of_cross_lt (cfg : RSAConfig U W) (u₁ u₂ : U) (w : W)
    (h : cfg.L1agent.score u₁ w * cfg.L1agent.totalScore u₂ <
         cfg.L1agent.score u₂ w * cfg.L1agent.totalScore u₁) :
    cfg.L1 u₁ w < cfg.L1 u₂ w :=
  cfg.L1agent.policy_lt_cross_of_cross_lt u₁ u₂ w h

/-- S1 same-state comparison via score comparison.

    Both sides share `(l, w)`, hence the same `S1agent.totalScore w`. -/
@[gcongr]
theorem S1_lt_of_score_lt (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (u₁ u₂ : U)
    (h : (cfg.S1agent l).score w u₁ < (cfg.S1agent l).score w u₂) :
    cfg.S1 l w u₁ < cfg.S1 l w u₂ :=
  (cfg.S1agent l).policy_lt_of_score_lt w u₁ u₂ h

/-- S1 same-state equality via score equality. -/
theorem S1_eq_of_score_eq (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (u₁ u₂ : U)
    (h : (cfg.S1agent l).score w u₁ = (cfg.S1agent l).score w u₂) :
    cfg.S1 l w u₁ = cfg.S1 l w u₂ :=
  (cfg.S1agent l).policy_eq_of_score_eq w u₁ u₂ h

/-- S1 cross-world comparison via cross-product (different `w` → different
    denominator). -/
@[gcongr]
theorem S1_lt_cross_of_cross_lt (cfg : RSAConfig U W) (l : cfg.Latent)
    (w₁ w₂ : W) (u : U)
    (h : (cfg.S1agent l).score w₁ u * (cfg.S1agent l).totalScore w₂ <
         (cfg.S1agent l).score w₂ u * (cfg.S1agent l).totalScore w₁) :
    cfg.S1 l w₁ u < cfg.S1 l w₂ u :=
  (cfg.S1agent l).policy_lt_cross_of_cross_lt w₁ w₂ u h

/-- L0 cross-world comparison via meaning comparison.

    Both sides share `(l, u)`, hence the same `L0agent.totalScore u`. The
    score IS the meaning, so this reduces to a comparison of meaning values. -/
@[gcongr]
theorem L0_lt_of_meaning_lt (cfg : RSAConfig U W) (l : cfg.Latent) (u : U)
    (w₁ w₂ : W)
    (h : cfg.meaning cfg.initial l u w₁ < cfg.meaning cfg.initial l u w₂) :
    cfg.L0 l u w₁ < cfg.L0 l u w₂ :=
  (cfg.L0agent l).policy_lt_of_score_lt u w₁ w₂ h

-- ============================================================================
-- §2. L1 score-shape unfolding
-- ============================================================================

/-- L1 score in closed form:
    `L1agent.score u w = worldPrior w · Σ_l latentPrior w l · S1 l w u`.

    This unfolds the `RationalAction.score` projection to the explicit sum,
    making the `worldPrior` and `latentPrior` factors visible for further
    structural reasoning. -/
theorem L1agent_score_eq (cfg : RSAConfig U W) (u : U) (w : W) :
    cfg.L1agent.score u w =
      cfg.worldPrior w * ∑ l : cfg.Latent, cfg.latentPrior w l * cfg.S1 l w u := rfl

/-- L1 score when the latent type has a unique inhabitant: the latent sum
    collapses to a single term, giving a clean three-factor product.

    Common case: most basic RSA models (Frank & Goodman 2012, Lassiter & Goodman
    2017, etc.) use no latent variable, i.e. `Latent = Unit`, which carries
    a `Unique` instance automatically. -/
theorem L1agent_score_unique_eq (cfg : RSAConfig U W) [Unique cfg.Latent]
    (u : U) (w : W) :
    cfg.L1agent.score u w =
      cfg.worldPrior w *
        cfg.latentPrior w default * cfg.S1 default w u := by
  rw [L1agent_score_eq, Fintype.sum_unique, ← mul_assoc]

-- ============================================================================
-- §3. S1 score-shape lemmas (parameterized by scoring rule)
-- ============================================================================

/-- Belief-based S1 score: monotonicity in `L0(u, w)`.

    For `s1Score = fun l0 α _ w u => Real.rpow (l0 u w) α`, the S1 score
    inherits strict monotonicity from `rpow _ α` (when α > 0).

    Application:
    ```
    -- Goal: (cfg.S1agent l).score w u₁ < (cfg.S1agent l).score w u₂
    apply S1_belief_score_lt_iff.mpr
    -- New goal: cfg.L0 l u₁ w < cfg.L0 l u₂ w
    ```

    The hypothesis `hShape` pins down the scoring rule; if your model uses
    a different `s1Score`, write a parallel lemma for that shape. -/
theorem S1_belief_score_lt_iff (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (u₁ u₂ : U)
    (hShape : ∀ l0 α l w u,
      cfg.s1Score l0 α l w u = Real.rpow (l0 u w) α) :
    (cfg.S1agent l).score w u₁ < (cfg.S1agent l).score w u₂ ↔
      Real.rpow (cfg.L0 l u₁ w) cfg.α < Real.rpow (cfg.L0 l u₂ w) cfg.α := by
  show cfg.s1Score (cfg.L0agent l).policy cfg.α l w u₁ <
       cfg.s1Score (cfg.L0agent l).policy cfg.α l w u₂ ↔ _
  rw [hShape, hShape]
  rfl

/-- Action-based S1 score: monotonicity in `α · (log L0 - cost)`.

    For `s1Score = fun l0 α _ w u => Real.exp (α * (Real.log (l0 u w) - cost u))`,
    the S1 score inherits strict monotonicity from `exp` and the linearity of
    `α · (log _ - cost _)`. -/
theorem S1_action_score_lt_iff (cfg : RSAConfig U W) (cost : U → ℝ)
    (l : cfg.Latent) (w : W) (u₁ u₂ : U)
    (hShape : ∀ l0 α _l w u,
      cfg.s1Score l0 α _l w u = Real.exp (α * (Real.log (l0 u w) - cost u))) :
    (cfg.S1agent l).score w u₁ < (cfg.S1agent l).score w u₂ ↔
      cfg.α * (Real.log (cfg.L0 l u₁ w) - cost u₁) <
      cfg.α * (Real.log (cfg.L0 l u₂ w) - cost u₂) := by
  show cfg.s1Score (cfg.L0agent l).policy cfg.α l w u₁ <
       cfg.s1Score (cfg.L0agent l).policy cfg.α l w u₂ ↔ _
  rw [hShape, hShape]
  exact Real.exp_lt_exp

end RSAConfig

end RSA
