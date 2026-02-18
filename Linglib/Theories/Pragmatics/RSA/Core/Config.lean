import Linglib.Theories.Pragmatics.RSA.Core.SpeakerUtility
import Linglib.Core.RationalAction

/-!
# RSAConfig — Unified RSA Configuration

A streamlined RSA configuration grounded in rational action theory. Each RSA
model decomposes into two orthogonal dimensions:

1. **What the agent optimizes** — the scoring rule (`SpeakerUtility`)
2. **What the observer marginalizes over** — the latent structure (`Latent`)

## Architecture

All three RSA levels are `RationalAction` instances:

    L0agent(l) : RationalAction U W    score(u, w) = meaning(l, u, w)
    S1agent(l) : RationalAction W U    score(w, u) = s1Score(L0.policy, α, w, u)
    L1agent    : RationalAction U W    score(u, w) = prior(w) · Σ_l prior(l) · S1(u|w,l)

L0 scores are just the meaning function — any prior the paper wants in L0
is baked into `meaning`. The empirical `worldPrior` (object salience, base
rates) enters only at L1, keeping L0 fixed under iterated updates.

S1 scores are computed by the pluggable `SpeakerUtility`:
- Belief-based (F&G 2012): score = L0(w|u)^α (via rpow; rpow(0,α)=0)
- Action-based (Q&F 2013): score = exp(α · L0(w|u))
- With cost: score = pureScore · exp(-α · cost(u))

## References

- Degen (2023). The Rational Speech Act Framework. §2.
- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
- Baker, Saxe & Tenenbaum (2009). Action Understanding as Inverse Planning.
- Qing & Franke (2013). Variations on a Bayesian Theme.
-/

namespace RSA

open BigOperators Core

-- ============================================================================
-- RSAConfig Structure
-- ============================================================================

/-- Unified RSA configuration.

Two orthogonal choices determine the model:
1. `speakerUtility` — what S1 computes (pluggable `SpeakerUtility`)
2. `Latent` — what L1 marginalizes over (generic type, default `Unit`)

S1 is a RationalAction whose score is computed by `speakerUtility.s1Score`.
The score function absorbs α, so S1 is not restricted to softmax form —
e.g., belief-based utility uses `rpow(L0, α)` which correctly zeros out
false utterances (rpow(0, α) = 0 for α > 0). -/
structure RSAConfig (U W : Type*) [Fintype U] [Fintype W] where
  /-- Latent variable type (default Unit for basic scenarios). -/
  Latent : Type := Unit
  /-- Fintype instance for Latent. -/
  [latentFintype : Fintype Latent]
  /-- Literal semantics φ(l, u, w) ≥ 0.
      This is L0's score function. Any prior the paper wants in L0
      should be baked in here (e.g. `prior(w) · ⟦u⟧(w)`). -/
  meaning : Latent → U → W → ℝ
  /-- Meaning values are non-negative. -/
  meaning_nonneg : ∀ l u w, 0 ≤ meaning l u w
  /-- Prior over latent variables (unnormalized). -/
  latentPrior : Latent → ℝ := fun _ => 1
  /-- Latent prior is non-negative. -/
  latentPrior_nonneg : ∀ l, 0 ≤ latentPrior l
  /-- Empirical prior over worlds (unnormalized).
      Enters only at L1, not L0. This is the object salience / base rate
      that the pragmatic listener uses for Bayesian inversion. -/
  worldPrior : W → ℝ := fun _ => 1
  /-- World prior is non-negative. -/
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w
  /-- Rationality parameter α > 0. -/
  α : ℝ
  /-- Rationality is positive. -/
  α_pos : 0 < α
  /-- Speaker utility function: what S1 computes. Each paper provides its own. -/
  speakerUtility : SpeakerUtility U W

attribute [instance] RSAConfig.latentFintype

variable {U W : Type*} [Fintype U] [Fintype W]

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

namespace RSAConfig

/-- L0 as a RationalAction (one per latent value).

L0 is the literal listener: given utterance u, score each world w by
meaning(l, u, w). The policy gives the normalized posterior L0(w|u, l).

The meaning function IS the score — any prior the paper wants in L0
is baked into `meaning`, not applied separately. This keeps L0 fixed
under iterated prior updates at L1. -/
noncomputable def L0agent (cfg : RSAConfig U W) (l : cfg.Latent) :
    RationalAction U W where
  score u w := cfg.meaning l u w
  score_nonneg u w := cfg.meaning_nonneg l u w

/-- L0 posterior: P(w|u, l) = meaning(l,u,w) / Σ_w' meaning(l,u,w'). -/
noncomputable def L0 (cfg : RSAConfig U W) (l : cfg.Latent) (u : U) (w : W) : ℝ :=
  (cfg.L0agent l).policy u w

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/-- S1 as a RationalAction.

S1's score is computed by `speakerUtility.s1Score`, which takes L0's
normalized posterior and the rationality parameter α. The score function
is pluggable — different papers provide different scoring rules:

- Belief-based: score = rpow(L0(w|u), α). Correct: rpow(0, α) = 0.
- Action-based: score = exp(α · L0(w|u)).
- With cost: score multiplied by exp(-α · cost(u)).

All softmax properties (S1 ∝ exp(α · U)) are special cases when
the score function happens to be exponential. -/
noncomputable def S1agent (cfg : RSAConfig U W) (l : cfg.Latent) :
    RationalAction W U where
  score w u := cfg.speakerUtility.s1Score (cfg.L0agent l).policy cfg.α w u
  score_nonneg _ _ := cfg.speakerUtility.s1Score_nonneg _ _ _ _
    (fun u' w' => (cfg.L0agent l).policy_nonneg u' w') cfg.α_pos

/-- S1 policy: P(u|w, l) = s1Score(L0, α, w, u) / Σ_u' s1Score(L0, α, w, u'). -/
noncomputable def S1 (cfg : RSAConfig U W) (l : cfg.Latent) (w : W) (u : U) : ℝ :=
  (cfg.S1agent l).policy w u

theorem S1_nonneg (cfg : RSAConfig U W) (l : cfg.Latent) (w : W) (u : U) :
    0 ≤ cfg.S1 l w u :=
  (cfg.S1agent l).policy_nonneg w u

theorem S1_sum_eq_one (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (h : (cfg.S1agent l).totalScore w ≠ 0) :
    ∑ u : U, cfg.S1 l w u = 1 :=
  (cfg.S1agent l).policy_sum_eq_one w h

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/-- L1 as a RationalAction.

The pragmatic listener inverts S1 via Bayes' rule, marginalizing over
latent variables. Score = prior(w) · Σ_l prior(l) · S1(u|w,l).

The empirical `worldPrior` enters here (not at L0), so L0 stays fixed
under iterated prior updates.

In reference games, L1 is choosing a target object.
In other settings, L1 is updating beliefs about the world.
Either way, the math is the same (Qing & Franke 2013). -/
noncomputable def L1agent (cfg : RSAConfig U W) :
    RationalAction U W where
  score u w := cfg.worldPrior w * ∑ l : cfg.Latent, cfg.latentPrior l * cfg.S1 l w u
  score_nonneg u w := mul_nonneg (cfg.worldPrior_nonneg w)
    (Finset.sum_nonneg fun l _ => mul_nonneg (cfg.latentPrior_nonneg l) (cfg.S1_nonneg l w u))

/-- L1 posterior: P(w|u) ∝ prior(w) · Σ_l prior(l) · S1(u|w,l). -/
noncomputable def L1 (cfg : RSAConfig U W) (u : U) (w : W) : ℝ :=
  cfg.L1agent.policy u w

/-- L1 posterior over latent variables: P(l|u) ∝ prior(l) · Σ_w prior(w) · S1(u|w,l). -/
noncomputable def L1_latent (cfg : RSAConfig U W) (u : U) (l : cfg.Latent) : ℝ :=
  let score := cfg.latentPrior l * ∑ w : W, cfg.worldPrior w * cfg.S1 l w u
  let total := ∑ l' : cfg.Latent, cfg.latentPrior l' * ∑ w : W, cfg.worldPrior w * cfg.S1 l' w u
  if total = 0 then 0 else score / total

end RSAConfig

end RSA
