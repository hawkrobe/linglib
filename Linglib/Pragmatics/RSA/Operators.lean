import Linglib.Core.Probability.Posterior
import Linglib.Pragmatics.RSA.SimpAttr
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# RSA — Unbundled Operators
[frank-goodman-2012] [degen-2023]

Mathlib-shaped, struct-free formulation of RSA's three core operators, sitting
as the library's RSA substrate. Each
operator takes its ingredients (meaning function, cost factor, rationality, prior)
as explicit arguments — no bundled-config projection chains, no nonneg-axiom fields.

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
`Core/Probability/Posterior.lean` — those cancel both the marginal
denominator AND the uniform prior in one move.

## Relationship to the retired bundled config

The bundled `RSAConfig` layer was retired once every study moved to these
operators; the pointwise API is now the sole RSA substrate.

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

/-- **Inequality decomposition for `L0OfMeaning`**: at a fixed utterance,
comparing two worlds' literal-listener probabilities reduces to comparing
their meaning values — the normalisation factor cancels. -/
@[rsa]
theorem L0OfMeaning_apply_lt_iff (meaning : U → W → ℝ≥0∞) (u : U)
    (h0 : ∑' w, meaning u w ≠ 0) (hTop : ∑' w, meaning u w ≠ ∞) (w₁ w₂ : W) :
    L0OfMeaning meaning u h0 hTop w₁ < L0OfMeaning meaning u h0 hTop w₂ ↔
      meaning u w₁ < meaning u w₂ :=
  PMF.normalize_lt_iff_lt _ _ _ _ _

/-- The `≤` companion of `L0OfMeaning_apply_lt_iff`. -/
@[rsa]
theorem L0OfMeaning_apply_le_iff (meaning : U → W → ℝ≥0∞) (u : U)
    (h0 : ∑' w, meaning u w ≠ 0) (hTop : ∑' w, meaning u w ≠ ∞) (w₁ w₂ : W) :
    L0OfMeaning meaning u h0 hTop w₁ ≤ L0OfMeaning meaning u h0 hTop w₂ ↔
      meaning u w₁ ≤ meaning u w₂ :=
  PMF.normalize_le_iff_le _ _ _ _ _

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

/-- Belief-based pragmatic speaker ([frank-goodman-2012]):
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
@[rsa]
theorem S1Belief_apply_lt_iff_score_lt (L0 : U → PMF W) (costFactor : U → ℝ≥0∞)
    (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u₁ u₂ : U) :
    S1Belief L0 costFactor α w h0 hTop u₁ < S1Belief L0 costFactor α w h0 hTop u₂ ↔
      (L0 u₁ w : ℝ≥0∞) ^ α * costFactor u₁ <
        (L0 u₂ w : ℝ≥0∞) ^ α * costFactor u₂ :=
  PMF.normalize_lt_iff_lt _ _ _ _ _

/-- The `≤` companion of `S1Belief_apply_lt_iff_score_lt`. -/
@[rsa]
theorem S1Belief_apply_le_iff_score_le (L0 : U → PMF W) (costFactor : U → ℝ≥0∞)
    (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u₁ u₂ : U) :
    S1Belief L0 costFactor α w h0 hTop u₁ ≤ S1Belief L0 costFactor α w h0 hTop u₂ ↔
      (L0 u₁ w : ℝ≥0∞) ^ α * costFactor u₁ ≤
        (L0 u₂ w : ℝ≥0∞) ^ α * costFactor u₂ :=
  PMF.normalize_le_iff_le _ _ _ _ _

/-- The `=` companion of `S1Belief_apply_lt_iff_score_lt`: score symmetry. -/
@[rsa]
theorem S1Belief_apply_eq_iff_score_eq (L0 : U → PMF W) (costFactor : U → ℝ≥0∞)
    (α : ℝ) (w : W)
    (h0 : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ 0)
    (hTop : ∑' u, (L0 u w : ℝ≥0∞) ^ α * costFactor u ≠ ∞) (u₁ u₂ : U) :
    S1Belief L0 costFactor α w h0 hTop u₁ = S1Belief L0 costFactor α w h0 hTop u₂ ↔
      (L0 u₁ w : ℝ≥0∞) ^ α * costFactor u₁ =
        (L0 u₂ w : ℝ≥0∞) ^ α * costFactor u₂ :=
  PMF.normalize_eq_iff_eq _ _ _ _ _

/-! ## S1: Pragmatic Speaker (softmax-of-expected-log form) -/

/-- [goodman-stuhlmuller-2013] / [kao-etal-2014-metaphor]-style speaker:
`S1(u | obs) ∝ exp(α · Σ_s belief(s) · log lex(u, s))` when `qOk u`, else 0.

Real-valued internally; lifted to `ℝ≥0∞` at the `PMF.normalize` boundary. The
quality predicate `qOk` is *not* derived from `lex` and `belief` because Lean's
`Real.log 0 = 0` does not match WebPPL's `log 0 = -∞`: in WebPPL the score is
automatically zero on quality-violating utterances (via `exp (-∞) = 0`), but
in Lean an explicit filter is required. Consumers typically pass
`qOk u := ∀ s ∈ supp belief, lex u s > 0` or a problem-specific predicate.

The score is positive iff `qOk u` (regardless of `lex`/`belief`
internals — `Real.exp` is always positive). The `tsum`-positivity cover
collapses to `∃ u, qOk u` (see `softmaxBelief_tsum_ne_zero_of_witness`),
which is the natural shape for a `PMF.normalize` discharge. -/
noncomputable def softmaxBelief [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (α : ℝ) (qOk : U → Prop) [DecidablePred qOk]
    (u : U) : ℝ≥0∞ :=
  if qOk u then
    ENNReal.ofReal (Real.exp (α * ∑ s : W, belief s * Real.log (lex u s)))
  else 0

theorem softmaxBelief_ne_top [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (α : ℝ) (qOk : U → Prop) [DecidablePred qOk]
    (u : U) :
    softmaxBelief lex belief α qOk u ≠ ∞ := by
  unfold softmaxBelief
  split <;> simp [ENNReal.ofReal_ne_top]

theorem softmaxBelief_tsum_ne_top [Fintype U] [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (α : ℝ) (qOk : U → Prop) [DecidablePred qOk] :
    ∑' u, softmaxBelief lex belief α qOk u ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun u => softmaxBelief_ne_top lex belief α qOk u

theorem softmaxBelief_ne_zero_of_qOk [Fintype W]
    {lex : U → W → ℝ} {belief : W → ℝ} {α : ℝ} {qOk : U → Prop} [DecidablePred qOk] {u : U}
    (h : qOk u) :
    softmaxBelief lex belief α qOk u ≠ 0 := by
  unfold softmaxBelief
  rw [if_pos h]
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- The score is `0` exactly when the quality predicate fails. The
companion to `softmaxBelief_ne_zero_of_qOk` (positive direction); the two
characterise the support of `softmaxBelief lex belief α qOk` as
`{u | qOk u}`. -/
theorem softmaxBelief_eq_zero_of_not_qOk [Fintype W]
    {lex : U → W → ℝ} {belief : W → ℝ} {α : ℝ} {qOk : U → Prop} [DecidablePred qOk] {u : U}
    (h : ¬ qOk u) :
    softmaxBelief lex belief α qOk u = 0 := by
  unfold softmaxBelief
  rw [if_neg h]

/-- Cover discharge: a single quality-OK witness is enough to make the
fan-out sum non-zero — the standard `PMF.normalize` precondition shape. -/
theorem softmaxBelief_tsum_ne_zero_of_witness [Fintype W]
    {lex : U → W → ℝ} {belief : W → ℝ} {α : ℝ} {qOk : U → Prop} [DecidablePred qOk]
    {u : U} (h : qOk u) :
    ∑' u', softmaxBelief lex belief α qOk u' ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨u, softmaxBelief_ne_zero_of_qOk h⟩

/-- **Softmax collapse at concentrated belief (α = 1)**: when the belief is a
Kronecker delta on a single world `s*`, the expected log collapses to a
single log term, and `exp ∘ log` cancels at any positive value. The score
becomes simply `lex u s*` (lifted via `ENNReal.ofReal`).

The hypothesis `qOk u → 0 < lex u s*` is the canonical "quality-OK
utterances are true at the speaker-believed world" condition — it ensures
`Real.log (lex u s*)` is well-defined (non-junk-zero) so that `exp ∘ log`
gives back `lex u s*` rather than `1`.

This is the bridge that lets transcendental softmax expressions reduce to
rational arithmetic in models with deterministic full-access observations
(e.g., [goodman-stuhlmuller-2013] at access `.a3`). -/
theorem softmaxBelief_concentrated_apply [Fintype W] [DecidableEq W]
    (lex : U → W → ℝ) (sStar : W) (qOk : U → Prop) [DecidablePred qOk] (u : U)
    (h : qOk u → 0 < lex u sStar) :
    softmaxBelief lex (fun s => if s = sStar then 1 else 0) 1 qOk u =
      if qOk u then ENNReal.ofReal (lex u sStar) else 0 := by
  unfold softmaxBelief
  split_ifs with h_qOk
  · congr 1
    rw [one_mul, Finset.sum_eq_single sStar]
    · simp only [if_pos, one_mul]
      exact Real.exp_log (h h_qOk)
    · intro s _ hs
      simp [hs]
    · intro h_not_mem
      exact absurd (Finset.mem_univ sStar) h_not_mem
  · rfl

/-- **Softmax collapse at lex uniform on belief support (α = 1)**: when `lex u`
takes the same positive value `v` on every world in the belief support, the
expected log collapses to `log v`, and `exp ∘ log` cancels to give `v`. The
score becomes `ENNReal.ofReal v` (lifted via `ENNReal.ofReal`).

Generalises `softmaxBelief_concentrated_apply` from a Kronecker-delta belief
to any belief whose support sits inside `lex u`'s level set at `v`. Captures
the natural property of uniform-on-extension lex functions: when `qOk` passes,
the speaker's belief support is contained in the utterance's extension, where
lex is uniformly `1/|extension|`.

The hypothesis `∑ s, belief s = 1` is the canonical "belief is a probability
distribution" assumption; combined with bilinearity of multiplication it lets
the constant `log v` factor out of the sum. -/
theorem softmaxBelief_uniform_on_support [Fintype W]
    (lex : U → W → ℝ) (belief : W → ℝ) (qOk : U → Prop) [DecidablePred qOk]
    (u : U) (v : ℝ)
    (h_qok : qOk u)
    (h_uniform : ∀ s, belief s ≠ 0 → lex u s = v)
    (h_pos : 0 < v)
    (h_sum : (∑ s, belief s) = 1) :
    softmaxBelief lex belief 1 qOk u = ENNReal.ofReal v := by
  unfold softmaxBelief
  rw [if_pos h_qok]
  congr 1
  rw [one_mul]
  have h_eq : ∀ s ∈ Finset.univ, belief s * Real.log (lex u s) = belief s * Real.log v := by
    intro s _
    by_cases hs : belief s = 0
    · simp [hs]
    · rw [h_uniform s hs]
  rw [Finset.sum_congr rfl h_eq, ← Finset.sum_mul, h_sum, one_mul]
  exact Real.exp_log h_pos

/-! ## L1: Pragmatic Listener -/

/-- Pragmatic listener: Bayesian inversion of the speaker kernel against the
world prior. *Defined* as `PMF.posterior`, so the "L1 = posterior" claim is
true by construction.

Mathlib calls this operator `posterior` (`Mathlib/Probability/Kernel/Posterior.lean`,
notation `κ†μ`). At the PMF level — without measure-theoretic typeclasses —
it is `PMF.posterior` from `Core/Probability/Posterior.lean`. This file
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
