import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Speaker Utility

Pluggable speaker utility for RSA. A `SpeakerUtility` determines the
pragmatic speaker S1's scoring rule: how L0's normalized posterior is
transformed into an S1 score.

## Architecture

A `SpeakerUtility U W` computes the S1 **score** — a non-negative value —
directly from L0's posterior, the rationality parameter α, the world w,
and the utterance u. S1's policy is then Luce choice over these scores:

    S1(u|w) = s1Score(L0, α, w, u) / Σ_u' s1Score(L0, α, w, u')

The score function absorbs both the utility transformation and the
rationality parameter, because the relationship between utility and
score varies across utility types:

- **Belief-based** (Frank & Goodman 2012): score = L0(w|u)^α
  Uses `rpow` so that false utterances (L0 = 0) get score 0.

- **Action-based** (Qing & Franke 2013): score = exp(α · L0(w|u))
  Linear in L0, exponentiated by α. False utterances get exp(0) = 1.

- **With cost**: score = pureScore · exp(-α · cost(u))
  Cost is folded into the score, not separated.

The `SpeakerUtility` structure isolates **what** S1 computes from the
rest of the RSA architecture (meaning, priors, latent variables).

## References

- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
- Qing & Franke (2013). Variations on a Bayesian Theme.
- Degen (2023). The Rational Speech Act Framework. §2.
-/

namespace RSA

/-- A speaker utility function: computes the S1 score.

The `s1Score` field takes:
- `l0 : U → W → ℝ` — L0's normalized posterior (non-negative)
- `α : ℝ` — rationality parameter (positive)
- `w : W` — the actual world state
- `u : U` — the utterance

and returns a non-negative score. S1's policy is Luce choice:
S1(u|w) = s1Score(L0, α, w, u) / Σ_u' s1Score(L0, α, w, u'). -/
structure SpeakerUtility (U W : Type*) [Fintype W] where
  /-- Compute S1 score from L0 posterior and rationality parameter. -/
  s1Score : (U → W → ℝ) → ℝ → W → U → ℝ
  /-- S1 scores are non-negative when L0 is non-negative and α > 0. -/
  s1Score_nonneg : ∀ (l0 : U → W → ℝ) (α : ℝ) (w : W) (u : U),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ s1Score l0 α w u

end RSA
