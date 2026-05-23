import Linglib.Core.Agent.RationalAction

/-!
# RSAConfig — Type Definition
@cite{degen-2023} @cite{frank-goodman-2012} @cite{bergen-levy-goodman-2016} @cite{kao-etal-2014-hyperbole} @cite{qing-franke-2013}

The `RSAConfig` structure: the unified type for RSA models. All operations,
theorems, and the BToM grounding live in `Basic.lean`. This file contains
only the structure declaration and the `latentFintype` instance attribute,
matching the mathlib `Defs.lean` + `Basic.lean` separation pattern.

Each RSA model decomposes into two orthogonal dimensions:

1. **What the agent optimizes** — the scoring rule (`s1Score`)
2. **What the observer marginalizes over** — the latent structure (`Latent`)

L0 scores are just the meaning function — any prior the paper wants in L0
is baked into `meaning`. The empirical `worldPrior` (object salience, base
rates) enters only at L1, keeping L0 fixed under iterated updates.
-/

namespace RSA

/-- Unified RSA configuration.

Three orthogonal choices determine the model:
1. `s1Score` — what S1 computes (inline scoring rule)
2. `Latent` — what L1 marginalizes over (generic type, default `Unit`)
3. `Ctx` — sequential context for incremental models (default `Unit` for one-shot)

S1 is a RationalAction whose score is computed by `s1Score`.
The score function absorbs α, so S1 is not restricted to softmax form —
e.g., belief-based utility uses `rpow(L0, α)` which correctly zeros out
false utterances (rpow(0, α) = 0 for α > 0).

The `s1Score` field takes a `Latent` parameter so that latent variables
can enter at the S1 level (e.g., QUD projection in @cite{kao-etal-2014-hyperbole})
rather than being forced into `meaning`.

## Sequential RSA

For incremental/sequential models (@cite{cohn-gordon-goodman-potts-2019},
@cite{waldon-degen-2021}), set `Ctx` to a context type (e.g., `List LexItem`),
provide `transition` and `initial`, and make `meaning` depend on context.
One-shot RSA is the special case `Ctx = Unit` with trivial transition.

The sequential API (`S1_at`, `trajectoryProb`) computes word-by-word
production probabilities and chains them via the product rule. The one-shot
API (`L0agent`, `S1agent`, `L1agent`) always uses `initial` as context. -/
structure RSAConfig (U W : Type*) [Fintype U] [Fintype W] where
  /-- Context type for sequential models. Default `Unit` for one-shot. -/
  Ctx : Type := Unit
  /-- Latent variable type (default Unit for basic scenarios). -/
  Latent : Type := Unit
  /-- Fintype instance for Latent. -/
  [latentFintype : Fintype Latent]
  /-- Literal semantics φ(ctx, l, u, w) ≥ 0.
      This is L0's score function. Any prior the paper wants in L0
      should be baked in here (e.g. `prior(w) · ⟦u⟧(w)`).
      The `ctx` parameter supports sequential models where meaning
      depends on discourse context. For one-shot models (Ctx = Unit),
      simply ignore it with `_`. -/
  meaning : Ctx → Latent → U → W → ℝ
  /-- Meaning values are non-negative. -/
  meaning_nonneg : ∀ c l u w, 0 ≤ meaning c l u w
  /-- S1 scoring rule: computes the pragmatic speaker's score.

      Takes L0's normalized posterior, the rationality parameter α,
      a latent variable value, the world, and the utterance.
      Returns a non-negative score. S1's policy is Luce choice:
      S1(u|w,l) = s1Score(L0, α, l, w, u) / Σ_u' s1Score(L0, α, l, w, u').

      Examples:
      - Belief-based: `fun l0 α _ w u => rpow (l0 u w) α`
      - Action-based: `fun l0 α _ w u => exp (α * (l0 u w - cost u))`
      - QUD-based: `fun l0 α q w u => exp (α * (Real.log (qudProject q (l0 u) w) - cost u))` -/
  s1Score : (U → W → ℝ) → ℝ → Latent → W → U → ℝ
  /-- S1 scores are non-negative when L0 is non-negative and α > 0. -/
  s1Score_nonneg : ∀ (l0 : U → W → ℝ) (α : ℝ) (l : Latent) (w : W) (u : U),
    (∀ u' w', 0 ≤ l0 u' w') → 0 < α → 0 ≤ s1Score l0 α l w u
  /-- Rationality parameter α > 0. -/
  α : ℝ
  /-- Rationality is positive. -/
  α_pos : 0 < α
  /-- Prior over latent variables (unnormalized), possibly world-dependent.
      Default: uniform (ignores world). World-dependent priors support models
      where the latent variable's distribution depends on the world state
      (e.g., observation probability conditioned on true state in
      @cite{goodman-stuhlmuller-2013}). -/
  latentPrior : W → Latent → ℝ := fun _ _ => 1
  /-- Latent prior is non-negative. -/
  latentPrior_nonneg : ∀ w l, 0 ≤ latentPrior w l
  /-- Empirical prior over worlds (unnormalized).
      Enters only at L1, not L0. This is the object salience / base rate
      that the pragmatic listener uses for Bayesian inversion. -/
  worldPrior : W → ℝ := fun _ => 1
  /-- World prior is non-negative. -/
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w
  /-- Context transition function. Maps current context and chosen utterance
      to the next context. Default: constant (one-shot, context never changes). -/
  transition : Ctx → U → Ctx := fun c _ => c
  /-- Initial context for sequential production. Default: `()` for one-shot. -/
  initial : Ctx := by exact ()

attribute [instance] RSAConfig.latentFintype

end RSA
