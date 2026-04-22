import Linglib.Core.Probability.PMFPosterior
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# RSA — Unbundled Operators
@cite{frank-goodman-2012} @cite{degen-2023}

Mathlib-shaped, struct-free formulation of RSA's three core operators, sitting
alongside the bundled `RSAConfig` API (`Defs.lean` / `Basic.lean`). Each
operator takes its ingredients (meaning function, cost factor, rationality, prior)
as explicit arguments — no `RSAConfig` projection chains, no nonneg-axiom fields.

The mathlib precedent is `bayesRisk` (`Mathlib/Probability/Decision/Risk/Defs.lean`):
```
def bayesRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) : ℝ≥0∞
```
There is no `BayesianDecisionConfig` struct. Ingredients are function arguments;
hypotheses are stated where needed; lemmas universally quantify over the parts
that vary.

## Operators

* `L0OfMeaning` — literal listener, normalising a non-negative meaning function
  `meaning : U → W → ℝ≥0∞` over worlds for each utterance.
* `S1Belief` — pragmatic speaker, belief-based form
  `S1(u | w) ∝ L0(w | u)^α · costFactor(u)`.
* `L1` — pragmatic listener, *defined* as `PMF.posterior` of the speaker kernel
  against the world prior. The grounding theorem `L1_eq_posterior` is `rfl`.

## Grounding

`L1` does not redefine Bayes' rule — it forwards to `PMF.posterior`. The
"L1 IS Bayesian inversion of S1 against the world prior" claim is therefore
true by construction (CLAUDE.md "import-don't-restipulate" discipline), not
by a bridge theorem proved after the fact. Theorems about `PMF.posterior`
(support characterisation, marginal-times-posterior identity) lift to `L1`
as one-liners.

## Relationship to `RSAConfig`

Phase 1 of the RSA → mathlib-PMF migration: this file is a pure addition.
`RSAConfig` and `RSAConfig.L1` (in `Basic.lean`) remain in place; consumer
code is unchanged. A subsequent phase migrates one Phenomena study end-to-end
to demonstrate that `rsa_predict` reflection still applies to operator
applications.
-/

set_option autoImplicit false

namespace RSA

variable {U W : Type*}

open scoped ENNReal

/-! ## L0: Literal Listener -/

/-- Literal listener built by normalising a meaning function over worlds.
For utterance `u`, `L0OfMeaning meaning u h0 h∞` is the PMF over worlds with
mass `meaning u w / Σ_{w'} meaning u w'`.

The two hypotheses are exactly `PMF.normalize`'s API: the marginal must be
non-zero (so the utterance is true *somewhere*) and finite (automatic on
`Fintype W` if every meaning value is `< ∞`). -/
noncomputable def L0OfMeaning (meaning : U → W → ℝ≥0∞) (u : U)
    (h0 : ∑' w, meaning u w ≠ 0) (h∞ : ∑' w, meaning u w ≠ ∞) : PMF W :=
  PMF.normalize (meaning u) h0 h∞

@[simp] theorem L0OfMeaning_apply (meaning : U → W → ℝ≥0∞) (u : U)
    (h0 : ∑' w, meaning u w ≠ 0) (h∞ : ∑' w, meaning u w ≠ ∞) (w : W) :
    L0OfMeaning meaning u h0 h∞ w = meaning u w * (∑' w', meaning u w')⁻¹ :=
  PMF.normalize_apply _ _ _ w

/-! ## S1: Pragmatic Speaker (belief-based) -/

/-- Belief-based pragmatic speaker (@cite{frank-goodman-2012}):
`S1(u | w) ∝ L0(w | u)^α · costFactor(u)`, normalised over utterances.

* `L0 : U → PMF W` — the literal listener kernel (often built via
  `L0OfMeaning`, but any kernel will do).
* `costFactor : U → ℝ≥0∞` — multiplicative cost weight. To recover the
  classical `exp(-cost)` form pass `fun u => ENNReal.ofReal (Real.exp (-cost u))`.
* `α : ℝ` — rationality / soft-max temperature.

Returns the speaker's distribution at world `w`. -/
noncomputable def S1Belief (L0 : U → PMF W) (costFactor : U → ℝ≥0∞) (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (h∞ : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) : PMF U :=
  PMF.normalize (fun u => (L0 u w : ℝ≥0∞) ^ α * costFactor u) h0 h∞

@[simp] theorem S1Belief_apply (L0 : U → PMF W) (costFactor : U → ℝ≥0∞) (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (h∞ : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u : U) :
    S1Belief L0 costFactor α w h0 h∞ u =
      (L0 u w : ℝ≥0∞) ^ α * costFactor u * (∑' u', (L0 u' w : ℝ≥0∞) ^ α * costFactor u')⁻¹ :=
  PMF.normalize_apply _ _ _ u

/-! ## L1: Pragmatic Listener -/

/-- Pragmatic listener: Bayesian inversion of the speaker kernel against the
world prior. *Defined* as `PMF.posterior`, so the "L1 = posterior" claim is
true by construction.

Mathlib calls this operator `posterior` (`Mathlib/Probability/Kernel/Posterior.lean`,
notation `κ†μ`). At the PMF level — without measure-theoretic typeclasses —
it is `PMF.posterior` from `Core/Probability/PMFPosterior.lean`. This file
gives it the linguistically familiar name `L1`. -/
noncomputable def L1 (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) : PMF W :=
  PMF.posterior speaker worldPrior u h

/-- Grounding theorem: `L1` IS `PMF.posterior`. True by construction (`rfl`),
not by a bridge proof. This is the point of the unbundled formulation — the
mathlib operator is the definition, not something we redefine and reconcile. -/
theorem L1_eq_posterior (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) :
    L1 speaker worldPrior u h = PMF.posterior speaker worldPrior u h := rfl

@[simp] theorem L1_apply (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) (w : W) :
    L1 speaker worldPrior u h w =
      worldPrior w * speaker w u * (PMF.marginal speaker worldPrior u)⁻¹ :=
  PMF.posterior_apply _ _ _ _ _

/-- Support of L1: a world has positive posterior mass iff it had positive
prior mass *and* the speaker assigns it positive probability of the
observed utterance. Lifts directly from `PMF.mem_support_posterior_iff`. -/
theorem mem_support_L1_iff (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) (w : W) :
    w ∈ (L1 speaker worldPrior u h).support ↔ worldPrior w ≠ 0 ∧ speaker w u ≠ 0 :=
  PMF.mem_support_posterior_iff _ _ _ _ _

/-- Bayes identity in product form: `marginal · L1 = prior · speaker`. Lifts
from `PMF.marginal_mul_posterior_apply`. -/
theorem marginal_mul_L1_apply (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) (w : W) :
    PMF.marginal speaker worldPrior u * L1 speaker worldPrior u h w =
      worldPrior w * speaker w u :=
  PMF.marginal_mul_posterior_apply _ _ _ _ _

end RSA
