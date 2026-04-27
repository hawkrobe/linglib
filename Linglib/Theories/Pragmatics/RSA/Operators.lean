import Linglib.Core.Probability.PMFPosterior
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Uniform

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

## Inequality decomposition (for consumer migrations)

Each operator has parallel `_lt_iff_score_lt` and `_le_iff_score_le` lemmas
that strip off the normalisation factor — the workhorses for migrating
"L1/S1 prefers a₂ over a₁" claims through the structural shell:

* `S1Belief_apply_lt_iff_score_lt` / `S1Belief_apply_le_iff_score_le` —
  same-world utterance comparison reduces to `(L0 u w)^α · cost u`
* `L1_lt_iff_score_lt` / `L1_le_iff_score_le` — same-observation world
  comparison reduces to `prior(w) · κ(w, u)`

For the common case where the world prior is uniform, see
`PMF.posterior_lt_iff_kernel_lt_of_uniform` / `_le_iff_kernel_le` in
`Core/Probability/PMFPosterior.lean` — those cancel both the marginal
denominator AND the uniform prior in one move.

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
For utterance `u`, `L0OfMeaning meaning u h0 hTop` is the PMF over worlds with
mass `meaning u w / Σ_{w'} meaning u w'`.

The two hypotheses are exactly `PMF.normalize`'s API: the marginal must be
non-zero (so the utterance is true *somewhere*) and finite (automatic on
`Fintype W` if every meaning value is `< ∞`). -/
noncomputable def L0OfMeaning (meaning : U → W → ℝ≥0∞) (u : U)
    (h0 : ∑' w, meaning u w ≠ 0) (hTop : ∑' w, meaning u w ≠ ∞) : PMF W :=
  PMF.normalize (meaning u) h0 hTop

-- Not `@[simp]`: introduces `(∑' w', ...)⁻¹`; use explicitly via `rw`.
theorem L0OfMeaning_apply (meaning : U → W → ℝ≥0∞) (u : U)
    (h0 : ∑' w, meaning u w ≠ 0) (hTop : ∑' w, meaning u w ≠ ∞) (w : W) :
    L0OfMeaning meaning u h0 hTop w = meaning u w * (∑' w', meaning u w')⁻¹ :=
  PMF.normalize_apply _ _ w

/-! ## L0 from a Boolean meaning (uniform on extension) -/

/-- Extension of a Boolean meaning at utterance `u`: the `Finset` of worlds
the meaning is true at. The `[Fintype W]`/`[DecidableEq W]` machinery is used
implicitly via `Finset.univ.filter`. -/
def extensionOf [Fintype W] (m : U → W → Bool) (u : U) : Finset W :=
  Finset.univ.filter (fun w => m u w)

@[simp] theorem mem_extensionOf [Fintype W] {m : U → W → Bool} {u : U} {w : W} :
    w ∈ extensionOf m u ↔ m u w = true := by
  simp [extensionOf]

/-- Literal listener for a Boolean meaning: uniform distribution on the
extension. Specialisation of `L0OfMeaning` to the case where each meaning
value is `0` or `1` and the extension is non-empty. The `(extensionOf m u).Nonempty`
hypothesis is `PMF.uniformOfFinset`'s API. -/
noncomputable def L0OfBoolMeaning [Fintype W] (m : U → W → Bool) (u : U)
    (h : (extensionOf m u).Nonempty) : PMF W :=
  PMF.uniformOfFinset (extensionOf m u) h

theorem L0OfBoolMeaning_apply_of_mem [Fintype W] {m : U → W → Bool} {u : U}
    (h : (extensionOf m u).Nonempty) {w : W} (hw : m u w = true) :
    L0OfBoolMeaning m u h w = ((extensionOf m u).card : ℝ≥0∞)⁻¹ :=
  PMF.uniformOfFinset_apply_of_mem _ (mem_extensionOf.mpr hw)

theorem L0OfBoolMeaning_apply_of_not_mem [Fintype W] {m : U → W → Bool} {u : U}
    (h : (extensionOf m u).Nonempty) {w : W} (hw : m u w ≠ true) :
    L0OfBoolMeaning m u h w = 0 :=
  PMF.uniformOfFinset_apply_of_notMem _ (fun hMem => hw (mem_extensionOf.mp hMem))

@[simp] theorem mem_support_L0OfBoolMeaning_iff [Fintype W] {m : U → W → Bool} {u : U}
    (h : (extensionOf m u).Nonempty) (w : W) :
    w ∈ (L0OfBoolMeaning m u h).support ↔ m u w = true := by
  rw [L0OfBoolMeaning, PMF.mem_support_uniformOfFinset_iff, mem_extensionOf]

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
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) : PMF U :=
  PMF.normalize (fun u => (L0 u w : ℝ≥0∞) ^ α * costFactor u) h0 hTop

-- Not `@[simp]`: introduces `(∑' u', ...)⁻¹`; use explicitly via `rw`.
theorem S1Belief_apply (L0 : U → PMF W) (costFactor : U → ℝ≥0∞) (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u : U) :
    S1Belief L0 costFactor α w h0 hTop u =
      (L0 u w : ℝ≥0∞) ^ α * costFactor u * (∑' u', (L0 u' w : ℝ≥0∞) ^ α * costFactor u')⁻¹ :=
  PMF.normalize_apply _ _ u

/-- The S1Belief PMF assigns positive probability to `u` iff the L0 score at
`u` and the cost factor at `u` are both non-zero (rpow of a positive finite
base is positive). Convenience for discharging "speaker assigns probability
to this utterance" obligations downstream. -/
theorem S1Belief_apply_ne_zero_of_pos (L0 : U → PMF W) (costFactor : U → ℝ≥0∞)
    (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) {u : U}
    (hL0 : L0 u w ≠ 0) (hcost : costFactor u ≠ 0) :
    S1Belief L0 costFactor α w h0 hTop u ≠ 0 := by
  rw [← PMF.mem_support_iff, S1Belief, PMF.mem_support_normalize_iff]
  apply mul_ne_zero _ hcost
  have hntop : L0 u w ≠ ⊤ := PMF.apply_ne_top _ _
  exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hL0) hntop).ne'

/-- **Inequality decomposition for `S1Belief`**: at a fixed world, comparing
two utterances' speaker probabilities reduces to comparing their unnormalised
scores `(L0 u w)^α · cost u`. The partition function depends on `w` but not
on `u`, so it cancels.

Direct lift from `PMF.normalize_lt_iff_lt`. The workhorse decomposition
lemma for "speaker prefers `u₂` over `u₁` at world `w`" proofs. -/
theorem S1Belief_apply_lt_iff_score_lt (L0 : U → PMF W) (costFactor : U → ℝ≥0∞)
    (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u₁ u₂ : U) :
    S1Belief L0 costFactor α w h0 hTop u₁ < S1Belief L0 costFactor α w h0 hTop u₂ ↔
      (L0 u₁ w : ℝ≥0∞) ^ α * costFactor u₁ <
        (L0 u₂ w : ℝ≥0∞) ^ α * costFactor u₂ :=
  PMF.normalize_lt_iff_lt _ _ _ _ _

/-- The `≤` companion of `S1Belief_apply_lt_iff_score_lt`. -/
theorem S1Belief_apply_le_iff_score_le (L0 : U → PMF W) (costFactor : U → ℝ≥0∞)
    (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u₁ u₂ : U) :
    S1Belief L0 costFactor α w h0 hTop u₁ ≤ S1Belief L0 costFactor α w h0 hTop u₂ ↔
      (L0 u₁ w : ℝ≥0∞) ^ α * costFactor u₁ ≤
        (L0 u₂ w : ℝ≥0∞) ^ α * costFactor u₂ :=
  PMF.normalize_le_iff_le _ _ _ _ _

/-! ## S1: Pragmatic Speaker (softmax-of-expected-log form) -/

/-- @cite{goodman-stuhlmuller-2013} / @cite{kao-etal-2014-metaphor}-style speaker:
`S1(u | obs) ∝ exp(α · Σ_s belief(s) · log lex(u, s))` when `qOk u`, else 0.

Real-valued internally; lifted to `ℝ≥0∞` at the `PMF.normalize` boundary. The
quality predicate `qOk` is *not* derived from `lex` and `belief` because Lean's
`Real.log 0 = 0` does not match WebPPL's `log 0 = -∞`: in WebPPL the score is
automatically zero on quality-violating utterances (via `exp (-∞) = 0`), but
in Lean an explicit filter is required. Consumers typically pass
`qOk u := ∀ s ∈ supp belief, lex u s > 0` or a problem-specific predicate.

The score is positive iff `qOk u = true` (regardless of `lex`/`belief`
internals — `Real.exp` is always positive). The `tsum`-positivity cover
collapses to `∃ u, qOk u` (see `softmaxBelief_tsum_ne_zero_of_witness`),
which is the natural shape for a `PMF.normalize` discharge. -/
noncomputable def softmaxBelief [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (α : ℝ) (qOk : U → Bool) (u : U) : ℝ≥0∞ :=
  if qOk u then
    ENNReal.ofReal (Real.exp (α * ∑ s : W, belief s * Real.log (lex u s)))
  else 0

theorem softmaxBelief_ne_top [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (α : ℝ) (qOk : U → Bool) (u : U) :
    softmaxBelief lex belief α qOk u ≠ ∞ := by
  unfold softmaxBelief
  split <;> simp [ENNReal.ofReal_ne_top]

theorem softmaxBelief_tsum_ne_top [Fintype U] [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (α : ℝ) (qOk : U → Bool) :
    ∑' u, softmaxBelief lex belief α qOk u ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => softmaxBelief_ne_top lex belief α qOk u

theorem softmaxBelief_ne_zero_of_qOk [Fintype W]
    {lex : U → W → ℝ} {belief : W → ℝ} {α : ℝ} {qOk : U → Bool} {u : U}
    (h : qOk u = true) :
    softmaxBelief lex belief α qOk u ≠ 0 := by
  unfold softmaxBelief
  rw [if_pos h]
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- Cover discharge: a single quality-OK witness is enough to make the
fan-out sum non-zero — the standard `PMF.normalize` precondition shape. -/
theorem softmaxBelief_tsum_ne_zero_of_witness [Fintype W]
    {lex : U → W → ℝ} {belief : W → ℝ} {α : ℝ} {qOk : U → Bool}
    {u : U} (h : qOk u = true) :
    ∑' u', softmaxBelief lex belief α qOk u' ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨u, softmaxBelief_ne_zero_of_qOk h⟩

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

-- Not `@[simp]`: introduces `(PMF.marginal ...)⁻¹`; use explicitly via `rw`.
theorem L1_apply (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
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

/-- **Inequality decomposition for L1**: posterior comparison at the pragmatic-
listener layer reduces to score comparison. Direct lift from
`PMF.posterior_lt_iff_score_lt` — the shared marginal denominator cancels.

This is the workhorse decomposition lemma for "world `w₁` has higher
posterior probability than world `w₂` after observing `u`" claims. -/
theorem L1_lt_iff_score_lt (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) (w₁ w₂ : W) :
    L1 speaker worldPrior u h w₁ < L1 speaker worldPrior u h w₂ ↔
      worldPrior w₁ * speaker w₁ u < worldPrior w₂ * speaker w₂ u :=
  PMF.posterior_lt_iff_score_lt _ _ _ _ _ _

/-- The `≤` companion of `L1_lt_iff_score_lt`. -/
theorem L1_le_iff_score_le (speaker : W → PMF U) (worldPrior : PMF W) (u : U)
    (h : PMF.marginal speaker worldPrior u ≠ 0) (w₁ w₂ : W) :
    L1 speaker worldPrior u h w₁ ≤ L1 speaker worldPrior u h w₂ ↔
      worldPrior w₁ * speaker w₁ u ≤ worldPrior w₂ * speaker w₂ u :=
  PMF.posterior_le_iff_score_le _ _ _ _ _ _

end RSA
