import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Theories.Pragmatics.RSA.LatentOperators
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{lassiter-goodman-2017} on mathlib `PMF` — structural shell
@cite{lassiter-goodman-2017}

L&G 2017 ("Adjectival vagueness in a Bayesian model of interpretation",
*Synthese* 194:3801-3836) gives a Bayesian/RSA account of vague gradable
adjectives. This file formalises the **structural skeleton** of that
account on mathlib's `PMF`, with explicit acknowledgment of what the
file does and does not capture.

## Scope (honest reckoning, post-audit)

L&G 2017's *novel* contribution is the **free-variable inference** of §4
(Eqs. 26-29): the L1 listener jointly infers the world `A` and the
threshold variable `V`, with marginalisation over thresholds (Eq. 30)
giving the height posterior. The paper's central empirical claims —
information transmission for vague terms (§4.3, Figs. 5-6),
context-sensitivity via prior shape (§4.4, Fig. 7, "tall building" vs.
"tall person"), antonym symmetry (Fig. 6), and the MC/PC/free-variable
sorites trichotomy (§5, Eqs. 36/38/41-44) — all live in that joint
posterior.

**This file does not formalise the joint posterior.** What it does:

1. Provides L&G-anchored *interpretive wrappers* for generic PMF
   theorems already promoted to `Core/Probability/PMFPosterior.lean`
   (the structural sorites bound, the borderline-as-intermediate-measure
   schema, posterior concentration).
2. Captures L&G's Eq. 32 outer-measure metalinguistic-probability
   formula directly via `PMF.toOuterMeasure`.
3. Documents the Frank-&-Goodman 2012 scalar-implicature mechanism that
   L&G use as a §3 warmup — clearly labelled as not L&G's novel
   contribution.

**Not yet captured (substrate gaps):**

- Joint inference over `(world, threshold)` (Eqs. 26-29).
- Height marginalisation (Eq. 30) producing the height posterior of §4.3.
- The MC/PC/free-variable trichotomy on sorites premises (Eqs. 36/38/41-44).
- Antonym symmetry (Eqs. 22-23, Fig. 6).
- The "informativity-prior tradeoff" balancing process (§4.3 prose).
- Adams's bound (`adams_uncertainty_bound`, deferred — verbose generic
  probability theorem, not RSA-specific; cf. § Note on Adams below).

## Connection to the bundled formalisation

The bundled-`RSAConfig` formalisation in `LassiterGoodman2017.lean`
(sibling file, in this directory) handles the empirical-fit reproduction
via `rsa_predict` reflection. Its `defaultCfg.L1 : Utterance → Height →
ℝ` returns unnormalised real values via the bundled API; it is not
PMF-shaped.

The two files are **deliberately complementary**, not bridged: this one
for the structural skeleton + cross-framework positioning, the bundled
one for numeric simulations of Figs. 5-10. A formal bridge would
require a PMF-shaped projection of `defaultCfg.L1` (currently absent
from the bundled API) and isn't load-bearing for either file's
contribution. The structural bounds proved here apply to *any* PMF over
thresholds, so any future PMF projection of `defaultCfg.L1` would
inherit them by construction.

## Geometry of the sorites bound

L&G 2017 Eq. 37 defines premise probability as an **integral over an
interval**:
```
P(x_m tall ∧ x_{m-1} not tall) = ∫_{h(x_{m-1})}^{h(x_m)} L1_latent(.tall) dθ
```
With grid spacing ε > 0 (e.g., ε = 0.5 inch in the Fig. 8 simulation),
each sorites gap corresponds to a *set* of thresholds, not a single
value. The discrete sum-over-singletons bound proved here
(`sorites_borderline_sum_le_one`) is the **single-point discretisation**
of Eq. 37; the full interval-additive form requires sigma-additivity of
`PMF.toOuterMeasure` on disjoint sets, which is true but not yet
factored out as a lemma. Stated as `sorites_premise_interval_sum_le_one`
below as a deferred sorry.

## Cross-framework positioning (linglib's "make incompatibilities visible")

L&G's probabilistic resolution of the sorites and characterisation of
borderline cases are *one* of several formalised positions in linglib:

* `Phenomena/Gradability/Studies/Fine1975.lean` — supervaluation,
  borderline mapped to `Truth3.indet`, sorites resolved by super-falsity
  of the inductive premise.
* `Linglib/Theories/Semantics/Supervaluation/TCS.lean` —
  Cobreros-Égré-Ripley-van-Rooij Tolerant/Strict/Classical, sorites
  resolved by non-transitivity of st-consequence.
* `Phenomena/Gradability/Studies/Klein1980.lean` — comparison-class
  delineation.
* `Phenomena/Gradability/Studies/Kennedy2007Licensing.lean` —
  standard-of-comparison contextualism.

Per linglib's "no bridge files" discipline, framework-comparison content
is anchored *here* (the chronologically-later paper) rather than in a
dedicated comparison file. The §7 theorem below proves the L&G
prediction, contrasts it with the @cite{alxatib-pelletier-2011}
borderline-contradiction data, and so makes the empirical incompatibility
between L&G's literal-meaning rule and the observed acceptance rate
visible at theorem level.

## Note on Adams's bound

L&G p. 25 cites Adams (1966) on cumulative uncertainty: "the uncertainty
of the consequent cannot exceed the sum of the uncertainties of the
premises." This is a generic probability theorem (`P(⋂ A_i) ≥
1 - ∑ (1 - P(A_i))`) with no RSA-specific content. Stated as
`adams_uncertainty_bound` (sorry'd) for completeness; the proof is a
verbose induction that belongs in mathlib's outer-measure library, not
here. L&G p. 27 (Eq. 38) also invokes a *different* Adams thesis ("The
Equation": `P(if A then B) = P(B|A)`), used for PC-sorites premise
strengths — neither captured.
-/

set_option autoImplicit false

namespace LassiterGoodman2017.PMF

open scoped ENNReal

variable {Threshold : Type*}

/-! ## §1. Sorites bound (singleton discretisation)

The discrete singleton sorites bound. Faithful to L&G 2017 §5
ARITHMETICALLY but uses a **single-point** approximation of Eq. 37's
interval integral. The general interval-additive form is below
(deferred). -/

/-- **Sorites resolution (singleton discretisation)**: for any threshold
posterior PMF and any finite set of distinct threshold values, the sum
of single-threshold probabilities is bounded by 1.

This is the discrete-grid approximation of L&G 2017 Eq. 37 with
grid-spacing ε such that each sorites gap corresponds to exactly one
threshold value. Faithful to the §5 *arithmetic* of the resolution
("the cumulative probability budget is bounded") but not to the *geometry*
(Eq. 37 sums measures of disjoint intervals, not singletons).

Wraps the generic `PMF.sum_finset_le_one` with L&G framing. -/
theorem sorites_borderline_sum_le_one (L1_latent : PMF Threshold)
    (s : Finset Threshold) :
    (∑ θ ∈ s, L1_latent θ) ≤ 1 :=
  L1_latent.sum_finset_le_one s

/-- **Sorites resolution (interval-additive form, faithful to Eq. 37)**:
for pairwise disjoint sorites-gap intervals `I θ`, the sum of
premise-event probabilities is bounded by 1.

This is the form L&G actually use in §5 — premise probability is
`L1_latent.toOuterMeasure (gap interval)`. The bound follows from
sigma-additivity of `PMF.toOuterMeasure` on disjoint sets +
`toOuterMeasure_apply_le_one` on the union.

Not yet proved: requires factoring out a sigma-additivity lemma for
`PMF.toOuterMeasure` on `Finset`-indexed disjoint sets, which deserves
its own `Core/Probability/` slot. The discrete singleton form
(`sorites_borderline_sum_le_one`) carries the §5 arithmetic; this form
captures the §5 geometry. -/
theorem sorites_premise_interval_sum_le_one (L1_latent : PMF Threshold)
    {β : Type*} (s : Finset β) (I : β → Set Threshold)
    (_h_disjoint : ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (I b) (I b')) :
    (∑ b ∈ s, L1_latent.toOuterMeasure (I b)) ≤ 1 := by
  sorry  -- TODO: PMF.toOuterMeasure_finset_sum_disjoint_le_one in Core/Probability/

/-! ## §2. Borderline as intermediate measure (L&G §4.4 closing argument)

The probabilistic characterisation of "borderline": the metalinguistic
probability `P_T(a is tall) = L1_latent.toOuterMeasure {θ | θ ≤ h(a)}`
is intermediate exactly when the threshold posterior straddles the
height being judged.

**Cross-framework note**: this characterisation is contested.
Supervaluation (`Fine1975.lean`) maps borderline to `Truth3.indet`;
epistemicism denies the very framing (borderline cases have determinate
Boolean truth values we don't know); TCS predicts borderline
contradictions are tolerantly *true*, with empirical support from
@cite{alxatib-pelletier-2011}. See `Phenomena/Gradability/Compare.lean`
for the comparison taxonomy. -/

/-- **Borderline-case theorem**: when both some threshold below `h` AND
some threshold ≥ `h` are in the posterior support, the metalinguistic
probability `P_T` is intermediate (`0 < P_T < 1`).

L&G's structural form of vagueness — but contested across frameworks.
See module docstring for cross-framework positioning. -/
theorem borderline_intermediate {S : Type*} (L1_latent : PMF S) (s : Set S)
    (h_witness_in : ∃ θ ∈ s, θ ∈ L1_latent.support)
    (h_witness_out : ∃ θ ∉ s, θ ∈ L1_latent.support) :
    0 < L1_latent.toOuterMeasure s ∧ L1_latent.toOuterMeasure s < 1 :=
  L1_latent.toOuterMeasure_pos_and_lt_one s h_witness_in h_witness_out

/-! ## §3. Pragmatic strengthening — Frank-Goodman 2012 mechanism

L&G 2017 §3 introduces this mechanism (Eqs. 14-20 with SOME/ALL) as a
**warmup** illustration of iterated rational reasoning. The genuinely
novel L&G L1 architecture is the §4 free-variable inference (Eqs.
28-29 — joint posterior over `(world, threshold)`), **NOT formalised
here**.

The theorem below captures the FG2012 scalar-implicature mechanism that
L&G use as exposition. It is genuinely RSA-architectural (depends on
rational speaker over alternatives + Bayesian listener), but does not
capture L&G's novel contribution. Anchored to L&G only because they
present this mechanism in §3; the canonical reference is
@cite{frank-goodman-2012}. -/

/-- **Pragmatic strengthening (FG2012 mechanism)**: when `u_weak` applies
at both `w_strong` and `w_only_weak` but a stronger alternative
`u_strong` applies only at `w_strong`, the listener posterior at
`u_weak` underspecifies `w_strong`. Generalised over arbitrary world
prior: requires the prior to assign equal weight to the two compared
worlds (the "neutral prior" assumption isolates the speaker-side
contribution).

The proof composes the promoted `posterior_lt_of_kernel_lt_of_prior_eq`
with `normalize_lt_of_apply_eq_of_sum_lt`. This is the FG2012
scalar-implicature mechanism, reframed at the L&G layer. -/
theorem pragmatic_strengthening {Utt World : Type*}
    (score : World → Utt → ℝ≥0∞)
    (h_score_top : ∀ w, ∑' u, score w u ≠ ∞)
    (h_score_pos : ∀ w, ∑' u, score w u ≠ 0)
    (S1 : World → PMF Utt)
    (h_S1 : ∀ w, S1 w = PMF.normalize (score w) (h_score_pos w) (h_score_top w))
    (worldPrior : PMF World)
    (u_weak : Utt) (w_strong w_only_weak : World)
    (h_marg : PMF.marginal S1 worldPrior u_weak ≠ 0)
    (h_eq : score w_strong u_weak = score w_only_weak u_weak)
    (h_pos_strong : score w_strong u_weak ≠ 0)
    (h_pos_strong_top : score w_strong u_weak ≠ ⊤)
    (h_partition_strict : ∑' u, score w_only_weak u < ∑' u, score w_strong u)
    (h_prior_eq : worldPrior w_strong = worldPrior w_only_weak)
    (h_prior_pos : worldPrior w_strong ≠ 0) :
    PMF.posterior S1 worldPrior u_weak h_marg w_strong <
      PMF.posterior S1 worldPrior u_weak h_marg w_only_weak := by
  have h_pos_only : score w_only_weak u_weak ≠ 0 := h_eq ▸ h_pos_strong
  have h_pos_only_top : score w_only_weak u_weak ≠ ⊤ := h_eq ▸ h_pos_strong_top
  apply PMF.posterior_lt_of_kernel_lt_of_prior_eq _ _ _ _ _ _ h_prior_eq h_prior_pos
  rw [h_S1 w_strong, h_S1 w_only_weak]
  exact PMF.normalize_lt_of_apply_eq_of_sum_lt _ _ _ _ _ _ _
    h_eq h_pos_only h_pos_only_top h_partition_strict

/-- **Iteration strictly strengthens L0**: corollary of `pragmatic_strengthening`.
The same asymmetric extensions that produce the strengthening also distinguish
`L1` from `L0`. -/
theorem iteration_strengthens {Utt World : Type*}
    (score : World → Utt → ℝ≥0∞)
    (h_score_top : ∀ w, ∑' u, score w u ≠ ∞)
    (h_score_pos : ∀ w, ∑' u, score w u ≠ 0)
    (S1 : World → PMF Utt)
    (h_S1 : ∀ w, S1 w = PMF.normalize (score w) (h_score_pos w) (h_score_top w))
    (worldPrior : PMF World)
    (u_weak : Utt) (w_strong w_only_weak : World)
    (h_marg : PMF.marginal S1 worldPrior u_weak ≠ 0)
    (h_eq : score w_strong u_weak = score w_only_weak u_weak)
    (h_pos_strong : score w_strong u_weak ≠ 0)
    (h_pos_strong_top : score w_strong u_weak ≠ ⊤)
    (h_partition_strict : ∑' u, score w_only_weak u < ∑' u, score w_strong u)
    (h_prior_eq : worldPrior w_strong = worldPrior w_only_weak)
    (h_prior_pos : worldPrior w_strong ≠ 0) :
    PMF.posterior S1 worldPrior u_weak h_marg w_strong ≠
      PMF.posterior S1 worldPrior u_weak h_marg w_only_weak :=
  ne_of_lt (pragmatic_strengthening score h_score_top h_score_pos S1 h_S1
    worldPrior u_weak w_strong w_only_weak h_marg h_eq
    h_pos_strong h_pos_strong_top h_partition_strict h_prior_eq h_prior_pos)

/-! ## §3'. Note on context-sensitivity (L&G §4.4)

L&G's §4.4 "skyscraper" passage characterises context-sensitivity via
**prior shape transfer to posterior shape** — the height prior for
"buildings" has a different mean and standard deviation than for
"people", and this propagates through the joint inference (Eqs. 28-29)
to a different threshold posterior, hence a different metalinguistic
probability of "tall".

A previous version of this file ("`prior_dominates_implicature`")
captured a much weaker claim: that a strongly-skewed prior on a single
world can override the kernel's pragmatic ranking on that world. That is
generic Bayes weighting (`posterior_lt_iff_score_lt`), not L&G's §4.4
claim about prior-shape transfer. The honest version requires the joint
posterior of Eqs. 28-29, which lives in the substrate gap (§4 of the
module docstring).

The generic Bayes-weighting result is `PMF.posterior_lt_iff_score_lt` in
`Core/Probability/PMFPosterior.lean` and is reusable for any consumer;
no L&G-specific wrapper here. -/

/-! ## §4. L&G Eq. 32 — metalinguistic probability as outer measure

L&G 2017 Eq. 32 (paper p. 22, verified):
```
P_T(a is tall) = ∫_0^{height(a)} P_L1(θ_tall | u = "a is tall") dθ_tall
```
The outer measure of `Set.Iio h` (thresholds at most `h`) under the
threshold posterior is the discrete analogue. No new theorem here; the
formal content is just `PMF.toOuterMeasure (Set.Iio h)`. -/

/-- **L&G Eq. 32 reference**: the metalinguistic probability of "a is
tall" is the threshold-posterior outer measure of thresholds ≤ height(a).

In code, this is just `L1_latent.toOuterMeasure (Set.Iio h)`. Stated as
an `example` (not a `def`) to anchor Eq. 32 without introducing a pure
rename. -/
example {S : Type*} [Preorder S] (L1_latent : PMF S) (h : S) :
    L1_latent.toOuterMeasure (Set.Iio h) = L1_latent.toOuterMeasure (Set.Iio h) := rfl

/-! ## §5. Adams's bound — generic probability, not RSA-specific

L&G p. 25 cites Adams (1966) on cumulative uncertainty:
```
1 - P(⋂ A_i) ≤ ∑ (1 - P(A_i))
```
or equivalently `P(⋂ A_i) ≥ 1 - ∑ (1 - P(A_i))`.

Generic probability theorem with no RSA-specific content; stated for
completeness, with proof deferred. The right home is mathlib's outer-
measure library, not here. -/

/-- **Adams's bound (cumulative uncertainty, generic)**: for any indexed
family of sets in a PMF, the measure of the intersection is bounded
below by `1 - ∑ (1 - measure(A_i))`. Generic probability theorem;
deferred. -/
theorem adams_uncertainty_bound {S : Type*} (p : PMF S)
    (sets : List (Set S)) :
    p.toOuterMeasure (sets.foldr (· ∩ ·) Set.univ) ≥
      (1 : ℝ≥0∞) - sets.foldr (fun A acc => acc + (1 - p.toOuterMeasure A)) 0 := by
  sorry  -- generic outer-measure bound, belongs in mathlib's library

/-! ## §6. Posterior concentration as fully-informative limit

When only one world has positive `prior · kernel` mass at observation
`u`, the posterior concentrates entirely on that world. The
deterministic limit of Bayesian update.

The theorem `posterior_eq_one_of_singleton_score_support` is in
`Core/Probability/PMFPosterior.lean`; it generalises the L&G "fully
informative L1 update" intuition without L&G framing. -/

example {Utt World : Type*}
    (S1 : World → PMF Utt) (worldPrior : PMF World) (u : Utt)
    (h_marg : PMF.marginal S1 worldPrior u ≠ 0)
    (w_unique : World)
    (h_unique : ∀ w', w' ≠ w_unique → worldPrior w' = 0 ∨ S1 w' u = 0) :
    PMF.posterior S1 worldPrior u h_marg w_unique = 1 :=
  PMF.posterior_eq_one_of_singleton_score_support S1 worldPrior u h_marg w_unique h_unique

/-! ## §7. Empirical contrast with @cite{alxatib-pelletier-2011}

L&G's literal-meaning prediction for "X is tall and X is not tall" — the
joint-Boolean conjunction of two complementary truth-conditional
contributions — is bounded by `P_T(tall) · (1 - P_T(tall)) ≤ 1/4`,
maximised at the maximally borderline `P_T = 1/2`.

Empirical contrast: @cite{alxatib-pelletier-2011} report **44.7%
acceptance** for "X is tall and not tall" applied to the median
(borderline) man in their visual stimulus. The data is encoded at
`Phenomena/Gradability/Vagueness.lean::alxatibPelletier2011Tall`.

`44.7% > 25%`, so a literal-meaning probabilistic account cannot
reproduce the data. This is the formal expression of the empirical
challenge that motivated TCS (`Linglib/Theories/Semantics/Supervaluation/TCS.lean`,
@cite{cobreros-etal-2012}), where borderline cases tolerantly satisfy
`P ∧ ¬P` *as a tolerantly-true proposition* — not via probability
multiplication.

This file does not formalise L&G's pragmatic enrichment of the literal
prediction (which would route through the joint posterior of Eqs.
28-29, in the substrate gap). The bound below is the literal-rule
prediction only. -/

/-- **L&G literal-rule borderline-contradiction bound**: under the
literal-meaning rule `P("X is P and not P") = P_T(P) · P_T(¬P)`, the
predicted acceptance is bounded by `1/4`, regardless of the underlying
threshold posterior or the height being judged.

Empirical contrast: @cite{alxatib-pelletier-2011} report 44.7% — well
above 25% — so the literal-rule prediction is empirically refuted.
TCS (`@cite{cobreros-etal-2012}`, formalised in
`Theories/Semantics/Supervaluation/TCS.lean`) accommodates the data via
non-probabilistic tolerant satisfaction. -/
theorem lg_literal_borderline_bounded {S : Type*} (L1_latent : PMF S) (s : Set S) :
    L1_latent.toOuterMeasure s * (1 - L1_latent.toOuterMeasure s) ≤ (1/4 : ℝ≥0∞) := by
  -- AM-GM on ENNReal for `p ∈ [0,1]`: `p · (1-p) ≤ 1/4`. Lift to `ℝ` via
  -- `toReal`, where the bound is `(2p - 1)² ≥ 0`.
  set p := L1_latent.toOuterMeasure s with hp_def
  have hp_le : p ≤ 1 := PMF.toOuterMeasure_apply_le_one _ _
  have hp_ne_top : p ≠ ⊤ := lt_of_le_of_lt hp_le ENNReal.one_lt_top |>.ne
  have h_one_minus_ne_top : 1 - p ≠ ⊤ :=
    ENNReal.sub_ne_top ENNReal.one_ne_top
  have h_prod_ne_top : p * (1 - p) ≠ ⊤ :=
    ENNReal.mul_ne_top hp_ne_top h_one_minus_ne_top
  -- Move to `ℝ` where `(2q - 1)² ≥ 0` gives the bound.
  rw [show (1/4 : ℝ≥0∞) = ENNReal.ofReal (1/4) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4),
            ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_toReal h_prod_ne_top]
  apply ENNReal.ofReal_le_ofReal
  rw [ENNReal.toReal_mul]
  set q := p.toReal with hq_def
  have hq_nonneg : 0 ≤ q := ENNReal.toReal_nonneg
  have hq_le_one : q ≤ 1 := by
    rw [hq_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from ENNReal.toReal_one.symm]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hp_le
  have h_sub_toReal : (1 - p).toReal = 1 - q := by
    rw [ENNReal.toReal_sub_of_le hp_le ENNReal.one_ne_top, ENNReal.toReal_one]
  rw [h_sub_toReal]
  -- Now: q * (1 - q) ≤ 1/4 on ℝ via (2q - 1)² ≥ 0
  nlinarith [sq_nonneg (2 * q - 1)]

end LassiterGoodman2017.PMF
