import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

/-!
# Bayesian Posterior on PMF

For a kernel `κ : α → PMF β` and prior `μ : PMF α`, the posterior at
observation `b` is the conditional distribution over `α` defined by
Bayes' rule:

  posterior κ μ b a = μ a * κ a b / ∑' a', μ a' * κ a' b

This is the PMF-level analogue of `ProbabilityTheory.posterior`
(`Mathlib.Probability.Kernel.Posterior`). Mathlib's `posterior` is
measure-theoretic and requires `[StandardBorelSpace]` /
`[IsFiniteKernel]`; this version operates directly on countably-
supported distributions and avoids the measure-theoretic typeclass
burden, at the cost of requiring an explicit positivity hypothesis
on the marginal at `b`.

## Main definitions

* `PMF.marginal κ μ b` — joint marginal `P(b) = ∑' a, μ a * κ a b`.
* `PMF.posterior κ μ b h` — posterior PMF over `α` given kernel `κ`,
  prior `μ`, observation `b`, and proof `h : marginal κ μ b ≠ 0`.

## Main statements

* `posterior_apply` — explicit Bayes formula.

## Inequality decomposition library

For each PMF construction, parallel `_lt_iff_lt` and `_le_iff_le` lemmas
strip off the normalisation factor — the foundation for "L1/posterior
prefers a₂ over a₁" structural proofs. Every construction has both
strict and non-strict forms with parallel naming:

* `normalize_lt_iff_lt` / `normalize_le_iff_le` — generic `PMF.normalize`
* `reweight_lt_iff_lt` / `reweight_le_iff_le` — reweight = normalize ∘ (· * w)
* `posterior_lt_iff_score_lt` / `posterior_le_iff_score_le` — Bayesian posterior

Sum-over-prior monotonicity (no iff — pointwise ≤ doesn't reverse):

* `marginal_le_marginal` / `marginal_lt_marginal` — `marginal κ μ b` over varying κ
* `bind_lt_bind` — same for `μ.bind f` shape

Specialization for the common "uniform world prior" case:

* `posterior_lt_iff_kernel_lt_of_uniform` / `posterior_le_iff_kernel_le_of_uniform` —
  cancels both the marginal denominator AND the uniform prior factor in one move

The bridge to `ProbabilityTheory.posterior` (via `PMF.toMeasure` /
`Measure.toKernel`) is left for a future file once a downstream
consumer needs the measure-theoretic identity.
-/

set_option autoImplicit false

open scoped ENNReal

namespace ENNReal

/-- On a finite type, an ENNReal `tsum` is finite iff every term is.
Convenience composition of `tsum_fintype` + `ENNReal.sum_ne_top` — the
combined form is the natural hypothesis shape for `PMF.normalize` /
`PMF.posterior` consumers. -/
theorem tsum_ne_top_of_fintype {α : Type*} [Fintype α] {f : α → ℝ≥0∞}
    (h : ∀ a, f a ≠ ∞) : ∑' a, f a ≠ ∞ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun a _ => h a

end ENNReal

namespace PMF

variable {α β : Type*}

/-- A finite-type kernel-marginal at `b` is finite. Convenience composition of
`PMF.apply_ne_top` over a Fintype index — the natural hypothesis shape for
consumers building `PMF.normalize` from a kernel slice. -/
theorem tsum_apply_ne_top [Fintype α] (κ : α → PMF β) (b : β) :
    ∑' a, κ a b ≠ ∞ :=
  ENNReal.tsum_ne_top_of_fintype fun _ => PMF.apply_ne_top _ _

/-- The marginal probability of observation `b` under the joint
distribution induced by kernel `κ` and prior `μ`:
`P(b) = ∑' a, μ a * κ a b`. -/
noncomputable def marginal (κ : α → PMF β) (μ : PMF α) (b : β) : ℝ≥0∞ :=
  ∑' a, μ a * κ a b

/-- A single witness `a` with `μ a ≠ 0` and `κ a b ≠ 0` suffices to make the
marginal non-zero — the standard positivity discharge for `PMF.posterior`. -/
theorem marginal_ne_zero (κ : α → PMF β) (μ : PMF α) (b : β)
    {a : α} (hμ : μ a ≠ 0) (hκ : κ a b ≠ 0) : marginal κ μ b ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨a, mul_ne_zero hμ hκ⟩

/-- Kernel-slice analogue of `marginal_ne_zero`: a single witness `a` with
`κ a b ≠ 0` makes the prior-free fan-out `∑' a', κ a' b` non-zero. The
shape consumers need when normalising the speaker step in RSA — there is
no listener prior over `α` to multiply against. -/
theorem tsum_apply_ne_zero (κ : α → PMF β) {a : α} {b : β} (h : κ a b ≠ 0) :
    ∑' a', κ a' b ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨a, h⟩

/-- Construct a `PMF` over a `Fintype` from a positive-finite weight
function, without requiring the user to verify `∑ a, f a = 1`. Mathlib's
`PMF.ofFintype` needs a normalisation equation; this variant accepts an
unnormalised function and renormalises, requiring only per-element
positivity (with at least one witness `a`) and per-element finiteness —
both reduced to per-element checks under the `Fintype` instance.

Closes the gap between `PMF.normalize` (general but requires `tsum`
discharges) and `PMF.ofFintype` (Finset-sum but requires `∑ = 1`). The
natural shape for prior construction from `ℚ`-valued probabilistic models. -/
noncomputable def normalizeOfFintype {α : Type*} [Fintype α] (f : α → ℝ≥0∞)
    (a : α) (h_pos : f a ≠ 0) (h_finite : ∀ a, f a ≠ ⊤) : PMF α :=
  PMF.normalize f
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨a, h_pos⟩)
    (ENNReal.tsum_ne_top_of_fintype h_finite)

private theorem marginal_le_one (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b ≤ 1 := by
  unfold marginal
  calc ∑' a, μ a * κ a b
      ≤ ∑' a, μ a := by
        refine ENNReal.tsum_le_tsum (fun a => ?_)
        calc μ a * κ a b ≤ μ a * 1 := mul_le_mul_right (PMF.coe_le_one _ _) _
          _ = μ a := mul_one _
    _ = 1 := PMF.tsum_coe μ

private theorem marginal_ne_top (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b ≠ ∞ :=
  (lt_of_le_of_lt (marginal_le_one κ μ b) ENNReal.one_lt_top).ne

/-- **Inequality decomposition for `PMF.normalize`**: comparing two normalised
values reduces to comparing the raw scores — the shared `(∑' x, f x)⁻¹` factor
cancels (it is positive and finite by the well-formedness hypotheses).

Foundation lemma for the structural-decomposition shell: every "speaker prefers
utterance u₂ over u₁ at world w" claim in RSA reduces to comparing unnormalised
scores via this lemma. The partition function depends on `w` but not on the
utterance being compared. -/
theorem normalize_lt_iff_lt {α : Type*} (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0)
    (hf : tsum f ≠ ∞) (a₁ a₂ : α) :
    normalize f hf0 hf a₁ < normalize f hf0 hf a₂ ↔ f a₁ < f a₂ := by
  rw [normalize_apply, normalize_apply]
  exact ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr hf)
    (ENNReal.inv_ne_top.mpr hf0)

/-- The `≤` companion of `normalize_lt_iff_lt`. -/
theorem normalize_le_iff_le {α : Type*} (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0)
    (hf : tsum f ≠ ∞) (a₁ a₂ : α) :
    normalize f hf0 hf a₁ ≤ normalize f hf0 hf a₂ ↔ f a₁ ≤ f a₂ := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact normalize_lt_iff_lt f hf0 hf a₂ a₁

/-- **Vacuous-zero cross-base inequality**: when the LHS normalize base
vanishes at `a` (`f a = 0`) and the RHS does not (`g a ≠ 0`), the LHS
normalize value is `0` and the RHS is positive — so the inequality holds.

This is the workhorse for "speaker-at-w₁ assigns zero mass to utterance `u`
because `u` is inapplicable, while speaker-at-w₂ assigns positive mass" —
exactly the pattern that arises in unique-reference RSA findings (e.g.,
"green only applies to green_square, so L1(.green) prefers .green_square").

The two normalize bases `f`, `g` correspond to S1 at different worlds. -/
theorem normalize_lt_of_apply_zero_pos {α : Type*}
    (f g : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)
    (hg0 : tsum g ≠ 0) (hg : tsum g ≠ ∞)
    (a : α) (ha : f a = 0) (hb : g a ≠ 0) :
    normalize f hf0 hf a < normalize g hg0 hg a := by
  rw [normalize_apply, normalize_apply, ha, zero_mul, pos_iff_ne_zero]
  exact mul_ne_zero hb (ENNReal.inv_ne_zero.mpr hg)

/-- **Cross-base equality**: when two normalize bases agree at `a` AND have
the same total sum, the normalized values are equal at `a`.

This is the canonical discharge for "S1 prefers utterance u equally at
worlds w₁ and w₂ because the QUD partition makes the speaker insensitive
to the choice" — exactly the pattern that arises in equality findings
(e.g., ScontrasPearl `surfAll`, `invHowMany`, `invAll` cases). -/
theorem normalize_eq_of_apply_eq_and_sum_eq {α : Type*}
    (f g : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)
    (hg0 : tsum g ≠ 0) (hg : tsum g ≠ ∞)
    (a : α) (h_apply : f a = g a) (h_sum : tsum f = tsum g) :
    normalize f hf0 hf a = normalize g hg0 hg a := by
  rw [normalize_apply, normalize_apply, h_apply, h_sum]

/-- **Cross-base ≤ via partition monotonicity**: when two normalize bases
agree at `a` (same numerator) and the LHS partition function dominates
(`tsum f ≥ tsum g` ⇒ LHS denominator larger ⇒ LHS quotient smaller), the
LHS normalized value is `≤` the RHS.

Useful for "S1 at world w₁ has same score for u as at w₂, but the
partition function at w₁ is larger because of an asymmetric distractor"
— canonical for ScontrasPearl `invNone` and similar rpow-monotonicity-
driven findings. -/
theorem normalize_le_of_apply_eq_and_sum_ge {α : Type*}
    (f g : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)
    (hg0 : tsum g ≠ 0) (hg : tsum g ≠ ∞)
    (a : α) (h_apply : f a = g a) (h_sum : tsum g ≤ tsum f) :
    normalize f hf0 hf a ≤ normalize g hg0 hg a := by
  rw [normalize_apply, normalize_apply, h_apply]
  -- Goal: g a * (tsum f)⁻¹ ≤ g a * (tsum g)⁻¹
  -- via mul_le_mul_left' (since g a ≥ 0) + ENNReal.inv_le_inv (tsum g ≤ tsum f → (tsum f)⁻¹ ≤ (tsum g)⁻¹)
  exact mul_le_mul_right (ENNReal.inv_le_inv.mpr h_sum) (g a)

/-- **Strict cross-base via partition strict-monotonicity**: when numerators
agree (`f a = g a`), the shared numerator is positive (`g a ≠ 0`, `≠ ⊤`),
and the LHS partition strictly dominates (`tsum g < tsum f`), then
`normalize f a < normalize g a`.

Strict companion of `normalize_le_of_apply_eq_and_sum_ge`. The positivity
hypothesis on `g a` is required for the cancellation to be strict — if
`g a = 0` both sides would equal 0 and the inequality wouldn't hold. -/
theorem normalize_lt_of_apply_eq_of_sum_lt {α : Type*}
    (f g : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)
    (hg0 : tsum g ≠ 0) (hg : tsum g ≠ ∞)
    (a : α) (h_apply : f a = g a) (h_pos : g a ≠ 0) (h_pos_top : g a ≠ ⊤)
    (h_sum : tsum g < tsum f) :
    normalize f hf0 hf a < normalize g hg0 hg a := by
  rw [normalize_apply, normalize_apply, h_apply]
  -- Goal: g a * (tsum f)⁻¹ < g a * (tsum g)⁻¹
  exact (ENNReal.mul_lt_mul_iff_right h_pos h_pos_top).mpr
    (ENNReal.inv_lt_inv.mpr h_sum)

-- Reweight: PMF × non-negative weight → PMF (the algebraic primitive
-- behind both Bayesian posterior and Product of Experts)

/-- Reweight a PMF by a non-negative weight function and renormalize.
The pointwise product `p · w` must have non-zero finite total mass —
the natural precondition for `PMF.normalize`.

This is the algebraic primitive that `posterior` and `productOfExperts`
both factor through: posterior takes `w := κ · b` (the kernel slice at
an observation), PoE takes `w := q ·` (the second PMF). -/
noncomputable def reweight (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) : PMF α :=
  PMF.normalize (fun a => p a * w a) h_pos h_fin

-- Not `@[simp]`: introduces `(∑' x, ...)⁻¹` which is rarely the desired
-- normal form. Apply explicitly via `rw` when needed.
theorem reweight_apply (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) (a : α) :
    p.reweight w h_pos h_fin a = p a * w a * (∑' x, p x * w x)⁻¹ :=
  PMF.normalize_apply _ _ _

theorem mem_support_reweight_iff (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) (a : α) :
    a ∈ (p.reweight w h_pos h_fin).support ↔ p a ≠ 0 ∧ w a ≠ 0 := by
  rw [reweight, mem_support_normalize_iff]
  exact mul_ne_zero_iff

/-- **Inequality decomposition for `PMF.reweight`**: the same denominator-
cancellation pattern, lifted via `reweight = normalize ∘ (· * w)`. Comparing
two reweighted values reduces to comparing the unnormalised products. -/
theorem reweight_lt_iff_lt (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) (a₁ a₂ : α) :
    p.reweight w h_pos h_fin a₁ < p.reweight w h_pos h_fin a₂ ↔
      p a₁ * w a₁ < p a₂ * w a₂ :=
  normalize_lt_iff_lt _ _ _ _ _

/-- The `≤` companion of `reweight_lt_iff_lt`. -/
theorem reweight_le_iff_le (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) (a₁ a₂ : α) :
    p.reweight w h_pos h_fin a₁ ≤ p.reweight w h_pos h_fin a₂ ↔
      p a₁ * w a₁ ≤ p a₂ * w a₂ :=
  normalize_le_iff_le _ _ _ _ _

/-- Bayesian posterior: for an observation `b`, the conditional
distribution over `α`. Well-defined when the marginal at `b` is
non-zero. The `≠ ∞` hypothesis is supplied automatically (the marginal
is bounded above by `1`). -/
noncomputable def posterior (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) : PMF α :=
  μ.reweight (fun a => κ a b) h (marginal_ne_top κ μ b)

theorem posterior_apply (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    posterior κ μ b h a = μ a * κ a b * (marginal κ μ b)⁻¹ := by
  show (μ.reweight _ _ _) a = _
  rw [reweight_apply]
  rfl

/-- The posterior is supported on the intersection of the prior's support
and the kernel's support at the observed `b`. -/
theorem mem_support_posterior_iff (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    a ∈ (posterior κ μ b h).support ↔ μ a ≠ 0 ∧ κ a b ≠ 0 :=
  mem_support_reweight_iff _ _ _ _ _

/-- Bayes' rule: the joint factors as marginal × posterior. -/
theorem marginal_mul_posterior_apply (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    marginal κ μ b * posterior κ μ b h a = μ a * κ a b := by
  rw [posterior_apply, ← mul_assoc, mul_comm (marginal κ μ b) (μ a * κ a b),
      mul_assoc, ENNReal.mul_inv_cancel h (marginal_ne_top κ μ b), mul_one]

/-- **Inequality decomposition**: posterior comparison reduces to score comparison.
The key lemma for proving inequalities about Bayesian posteriors structurally —
two posteriors at observation `b` agree on which world has more probability iff
the unnormalized scores `μ · κ` agree.

This is the inequality-side counterpart to `posterior_apply`: the latter says
*what* the posterior value is; this says how to *compare* two posterior values
without computing the marginal denominator (it cancels).

Mathlib precedent: similar to `Finset.sum_lt_sum_iff_of_le` style — the shared
denominator/normalizer cancels in the comparison. -/
theorem posterior_lt_iff_score_lt {α β : Type*} (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a₁ a₂ : α) :
    posterior κ μ b h a₁ < posterior κ μ b h a₂ ↔ μ a₁ * κ a₁ b < μ a₂ * κ a₂ b := by
  rw [posterior_apply, posterior_apply]
  -- Both sides are (μ · κ) * (marginal)⁻¹; the inverse is positive finite, so
  -- multiplication preserves < (use ENNReal.mul_lt_mul_iff_left, "right factor cancels").
  exact ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr (marginal_ne_top κ μ b))
    (ENNReal.inv_ne_top.mpr h)

/-- The `≤` companion of `posterior_lt_iff_score_lt`. -/
theorem posterior_le_iff_score_le {α β : Type*} (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a₁ a₂ : α) :
    posterior κ μ b h a₁ ≤ posterior κ μ b h a₂ ↔ μ a₁ * κ a₁ b ≤ μ a₂ * κ a₂ b := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact posterior_lt_iff_score_lt κ μ b h a₂ a₁

/-- **Chained-posterior decomposition** (PMF analogue of mathlib's
`Mathlib.Probability.Kernel.Posterior.posterior_comp`): comparing two
sequentially-updated posteriors `posterior κ₂ (posterior κ₁ μ b₁) b₂` at
two different points reduces to comparing products of unnormalised scores
`μ a · κ₁ a b₁ · κ₂ a b₂`.

Both intermediate normalisations cancel: the outer `marginal` cancels via
`posterior_lt_iff_score_lt`; the inner `marginal` factors out as a shared
`(marginal κ₁ μ b₁)⁻¹` on both sides of the inequality and cancels via
`mul_lt_mul_iff_left`. The result is "Bayes' rule for two conditionally-
independent observations sharing a prior".

Used in chained-RSA models like @cite{nouwen-2024}'s intersective
intensifier inference (paper Eq. 73): first update Π = stage-1 L1, then
second update against Π. Mathlib has the `Kernel`-categorical version
(`posterior_comp`); this is the discrete-PMF analogue. -/
theorem posterior_chained_lt_iff_score_lt {α β γ : Type*}
    (μ : PMF α) (κ₁ : α → PMF β) (κ₂ : α → PMF γ)
    (b₁ : β) (b₂ : γ)
    (h₁ : marginal κ₁ μ b₁ ≠ 0)
    (h₂ : marginal κ₂ (posterior κ₁ μ b₁ h₁) b₂ ≠ 0)
    (a a' : α) :
    posterior κ₂ (posterior κ₁ μ b₁ h₁) b₂ h₂ a <
      posterior κ₂ (posterior κ₁ μ b₁ h₁) b₂ h₂ a' ↔
        μ a * κ₁ a b₁ * κ₂ a b₂ < μ a' * κ₁ a' b₁ * κ₂ a' b₂ := by
  rw [posterior_lt_iff_score_lt, posterior_apply, posterior_apply]
  -- Goal: (μ a * κ₁ a b₁ * (marginal)⁻¹) * κ₂ a b₂ <
  --       (μ a' * κ₁ a' b₁ * (marginal)⁻¹) * κ₂ a' b₂
  --     ↔ μ a * κ₁ a b₁ * κ₂ a b₂ < μ a' * κ₁ a' b₁ * κ₂ a' b₂
  -- Rearrange via mul_right_comm to factor (marginal)⁻¹ to the right
  rw [mul_right_comm (μ a * κ₁ a b₁), mul_right_comm (μ a' * κ₁ a' b₁)]
  exact ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr (marginal_ne_top κ₁ μ b₁))
    (ENNReal.inv_ne_top.mpr h₁)

/-- **Marginal monotonicity (≤)**: if `κ₁ a b ≤ κ₂ a b` pointwise, then
`marginal κ₁ μ b ≤ marginal κ₂ μ b`. The prior `μ` is the same on both sides;
multiplying by it preserves the pointwise inequality, and `tsum` is monotone.

Foundation lemma for cross-utterance / cross-kernel marginal comparisons. -/
@[gcongr]
theorem marginal_le_marginal {α β : Type*} {κ₁ κ₂ : α → PMF β} {μ : PMF α}
    {b : β} (h : ∀ a, κ₁ a b ≤ κ₂ a b) :
    marginal κ₁ μ b ≤ marginal κ₂ μ b :=
  ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) (μ a))

/-- **Marginal monotonicity (<)**: if `κ₁ a b ≤ κ₂ a b` pointwise *and* the
inequality is strict at some `a₀` with positive prior mass, then
`marginal κ₁ μ b < marginal κ₂ μ b` strictly. Lifts `ENNReal.tsum_lt_tsum`
with the prior multiplier supplying both directions of the cancellation.

Use case: "speaker assigns higher probability to `u` at world `w₀` (and no
less anywhere else) — therefore the marginal probability of utterance `u`
strictly increases." -/
@[gcongr]
theorem marginal_lt_marginal {α β : Type*} {κ₁ κ₂ : α → PMF β} {μ : PMF α}
    {b : β} {a₀ : α} (hμ : μ a₀ ≠ 0) (h : ∀ a, κ₁ a b ≤ κ₂ a b)
    (hi : κ₁ a₀ b < κ₂ a₀ b) :
    marginal κ₁ μ b < marginal κ₂ μ b := by
  apply ENNReal.tsum_lt_tsum (marginal_ne_top κ₁ μ b)
    (fun a => mul_le_mul_right (h a) (μ a))
  exact ENNReal.mul_lt_mul_right hμ (PMF.apply_ne_top _ _) hi

/-- **Bind monotonicity (<)**: a `bind`-shape lift of `marginal_lt_marginal`.
If `f a b ≤ g a b` pointwise *and* the inequality is strict at some `a₀`
with positive prior mass, then `(μ.bind f) b < (μ.bind g) b`.

Direct lift via `bind_apply` — both sides unfold to the same shape that
`marginal_lt_marginal` consumes. Convenient for consumers using `PMF.bind`
directly (the mathlib monadic idiom) rather than the `marginal`-style
explicit-sum form.

(Not `@[gcongr]`-tagged — `f` and `g` appear as explicit args of `μ.bind`,
and gcongr requires varying arguments to be free variables.) -/
theorem bind_lt_bind {α β : Type*} (μ : PMF α) (f g : α → PMF β) (b : β)
    {a₀ : α} (hμ : μ a₀ ≠ 0) (h : ∀ a, f a b ≤ g a b) (hi : f a₀ b < g a₀ b) :
    μ.bind f b < μ.bind g b := by
  rw [bind_apply, bind_apply]
  exact marginal_lt_marginal hμ h hi

/-- **Posterior comparison under uniform prior**: the workhorse for any RSA
model with a uniform world prior. The shared prior factor `(card α)⁻¹` is
positive and finite, so it cancels — leaving a pure kernel comparison.

This is the right starting move for "L1 prefers world `a₂` over world `a₁`
after observing `b`" claims when the prior is `PMF.uniformOfFintype α`. -/
theorem posterior_lt_iff_kernel_lt_of_uniform {α β : Type*} [Fintype α] [Nonempty α]
    (κ : α → PMF β) (b : β)
    (h : marginal κ (PMF.uniformOfFintype α) b ≠ 0) (a₁ a₂ : α) :
    posterior κ (PMF.uniformOfFintype α) b h a₁ <
    posterior κ (PMF.uniformOfFintype α) b h a₂ ↔
      κ a₁ b < κ a₂ b := by
  rw [posterior_lt_iff_score_lt, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  -- Cancel the shared (Fintype.card α : ℝ≥0∞)⁻¹ factor. Need it positive (card ≠ ⊤,
  -- automatic for Nat-coerced ENNReal) and finite (card ≠ 0, from Nonempty α).
  have hcard_ne_zero : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have hcard_ne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr hcard_ne_top)
    (ENNReal.inv_ne_top.mpr hcard_ne_zero)

/-- The `≤` companion of `posterior_lt_iff_kernel_lt_of_uniform`. Required for
"negative" findings of the form `¬ L1 a₁ > L1 a₂` (canceled implicatures),
which reduce via `not_lt` to `L1 a₁ ≤ L1 a₂`. -/
theorem posterior_le_iff_kernel_le_of_uniform {α β : Type*} [Fintype α] [Nonempty α]
    (κ : α → PMF β) (b : β)
    (h : marginal κ (PMF.uniformOfFintype α) b ≠ 0) (a₁ a₂ : α) :
    posterior κ (PMF.uniformOfFintype α) b h a₁ ≤
    posterior κ (PMF.uniformOfFintype α) b h a₂ ↔
      κ a₁ b ≤ κ a₂ b := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact posterior_lt_iff_kernel_lt_of_uniform κ b h a₂ a₁

/-- **Cross-observation Bayes factor (iff)**: comparing two posteriors at
the SAME world but DIFFERENT observations is equivalent to a cross-multiplied
score comparison. The two marginals don't cancel (they're different) — instead
they cross-multiply.

This is the "competition at the boundary" pattern in RSA: `L1 u₁ w > L1 u₂ w`
where both u₁ and u₂ apply at the same world. Used in
@cite{kennedy-2015}-style findings for boundary numerals.

The `μ a` cancellation requires `μ a ≠ 0` and `≠ ⊤`. -/
private theorem posterior_cross_obs_lt_iff {α β : Type*} (κ : α → PMF β) (μ : PMF α) (a : α)
    (b₁ b₂ : β) (h₁ : marginal κ μ b₁ ≠ 0) (h₂ : marginal κ μ b₂ ≠ 0)
    (hμ : μ a ≠ 0) (hμ_top : μ a ≠ ⊤) :
    posterior κ μ b₁ h₁ a < posterior κ μ b₂ h₂ a ↔
      κ a b₁ * marginal κ μ b₂ < κ a b₂ * marginal κ μ b₁ := by
  -- The proof is an equivalence chain: multiply both sides of the LHS by
  -- (marginal b₁ * marginal b₂), use marginal_mul_posterior_apply, then
  -- cancel μ a. Each step is an iff.
  rw [show posterior κ μ b₁ h₁ a < posterior κ μ b₂ h₂ a ↔
        (marginal κ μ b₁ * marginal κ μ b₂) * posterior κ μ b₁ h₁ a <
        (marginal κ μ b₁ * marginal κ μ b₂) * posterior κ μ b₂ h₂ a from
      (ENNReal.mul_lt_mul_iff_right (mul_ne_zero h₁ h₂)
        (ENNReal.mul_ne_top (marginal_ne_top κ μ b₁) (marginal_ne_top κ μ b₂))).symm]
  rw [show (marginal κ μ b₁ * marginal κ μ b₂) * posterior κ μ b₁ h₁ a =
        marginal κ μ b₂ * (marginal κ μ b₁ * posterior κ μ b₁ h₁ a) from by ring,
      show (marginal κ μ b₁ * marginal κ μ b₂) * posterior κ μ b₂ h₂ a =
        marginal κ μ b₁ * (marginal κ μ b₂ * posterior κ μ b₂ h₂ a) from by ring,
      marginal_mul_posterior_apply κ μ b₁ h₁,
      marginal_mul_posterior_apply κ μ b₂ h₂]
  -- Goal: marginal b₂ * (μ a * κ a b₁) < marginal b₁ * (μ a * κ a b₂)
  --       ↔ κ a b₁ * marginal b₂ < κ a b₂ * marginal b₁
  rw [show marginal κ μ b₂ * (μ a * κ a b₁) = μ a * (κ a b₁ * marginal κ μ b₂) from by ring,
      show marginal κ μ b₁ * (μ a * κ a b₂) = μ a * (κ a b₂ * marginal κ μ b₁) from by ring]
  exact ENNReal.mul_lt_mul_iff_right hμ hμ_top

/-- Forward direction of `posterior_cross_obs_lt_iff` (convenience for the
common case where consumers have the cross-multiplied score inequality). -/
theorem posterior_lt_of_score_cross_lt {α β : Type*} (κ : α → PMF β) (μ : PMF α) (a : α)
    (b₁ b₂ : β) (h₁ : marginal κ μ b₁ ≠ 0) (h₂ : marginal κ μ b₂ ≠ 0)
    (hμ : μ a ≠ 0) (hμ_top : μ a ≠ ⊤)
    (h_cross : κ a b₁ * marginal κ μ b₂ < κ a b₂ * marginal κ μ b₁) :
    posterior κ μ b₁ h₁ a < posterior κ μ b₂ h₂ a :=
  (posterior_cross_obs_lt_iff κ μ a b₁ b₂ h₁ h₂ hμ hμ_top).mpr h_cross

/-! ## Outer-measure bounds

`PMF.toOuterMeasure` is bounded by 1 on every set, with strict inequality
characterised by support membership. These lemmas package the
`pos_iff_ne_zero` + `toOuterMeasure_apply_eq_zero_iff` pattern that arises
whenever a posterior measure is shown to be intermediate (`0 < · < 1`) —
the structural form of "borderline" in probabilistic vagueness models. -/

/-- `PMF.toOuterMeasure` of any set is at most `1`. The total mass is `1`,
and the indicator restriction is dominated pointwise by the PMF. -/
theorem toOuterMeasure_apply_le_one {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ 1 := by
  rw [toOuterMeasure_apply]
  calc (∑' x, s.indicator (⇑p) x)
      ≤ ∑' x, p x := ENNReal.tsum_le_tsum (fun x => Set.indicator_le_self _ _ x)
    _ = 1 := p.tsum_coe

/-- A `Finset` partial sum of a PMF is at most `1`. Specialisation of
`tsum_coe = 1` to a finite subset of the support — the discrete analogue
of "the integral of a probability density over any set is ≤ 1". -/
theorem sum_finset_le_one {α : Type*} (p : PMF α) (s : Finset α) :
    (∑ a ∈ s, p a) ≤ 1 :=
  (ENNReal.sum_le_tsum s).trans p.tsum_coe.le

/-- `PMF.toOuterMeasure` is strictly positive on any set that intersects
the support. This is the "lower-bound half" of intermediacy: a probabilistic
account of vagueness identifies "borderline" with `0 < toOuterMeasure < 1`. -/
private theorem toOuterMeasure_pos_of_exists_mem_support {α : Type*} (p : PMF α) (s : Set α)
    (h : ∃ a ∈ s, a ∈ p.support) : 0 < p.toOuterMeasure s := by
  rw [pos_iff_ne_zero, ne_eq, toOuterMeasure_apply_eq_zero_iff]
  intro h_disjoint
  obtain ⟨a, haS, haSupp⟩ := h
  exact h_disjoint.ne_of_mem haSupp haS rfl

/-- `PMF.toOuterMeasure` is strictly less than `1` on any set whose
complement intersects the support. The "upper-bound half" of intermediacy. -/
private theorem toOuterMeasure_lt_one_of_exists_not_mem {α : Type*} (p : PMF α) (s : Set α)
    (h : ∃ a ∉ s, a ∈ p.support) : p.toOuterMeasure s < 1 := by
  rw [lt_iff_le_and_ne]
  refine ⟨toOuterMeasure_apply_le_one p s, ?_⟩
  intro h_eq_one
  rw [toOuterMeasure_apply_eq_one_iff] at h_eq_one
  obtain ⟨a, haNotS, haSupp⟩ := h
  exact haNotS (h_eq_one haSupp)

/-- Combined intermediacy: when the support straddles `s` (witnesses both
in and out), the outer measure is strictly between `0` and `1`. -/
theorem toOuterMeasure_pos_and_lt_one {α : Type*} (p : PMF α) (s : Set α)
    (h_in : ∃ a ∈ s, a ∈ p.support) (h_out : ∃ a ∉ s, a ∈ p.support) :
    0 < p.toOuterMeasure s ∧ p.toOuterMeasure s < 1 :=
  ⟨toOuterMeasure_pos_of_exists_mem_support p s h_in,
   toOuterMeasure_lt_one_of_exists_not_mem p s h_out⟩

/-! ## Posterior degeneracy

The Bayesian posterior concentrates on a single point when the kernel and
prior conspire to leave only one positive-score world. Conversely, when
the prior assigns equal mass to two worlds, the posterior ordering tracks
the kernel ordering. -/

/-- **Posterior concentrates on a singleton score-support**: if every
`a' ≠ a_unique` has either zero prior or zero kernel value at `b`, then
`posterior κ μ b a_unique = 1`. The deterministic limit of Bayesian
update — full information transmission. -/
theorem posterior_eq_one_of_singleton_score_support {α β : Type*}
    (κ : α → PMF β) (μ : PMF α) (b : β)
    (h_marg : marginal κ μ b ≠ 0) (a_unique : α)
    (h_unique : ∀ a', a' ≠ a_unique → μ a' = 0 ∨ κ a' b = 0) :
    posterior κ μ b h_marg a_unique = 1 := by
  rw [posterior_apply]
  have h_marg_eq : marginal κ μ b = μ a_unique * κ a_unique b := by
    unfold marginal
    rw [tsum_eq_single a_unique]
    intro a' ha'
    rcases h_unique a' ha' with h | h
    · simp [h]
    · simp [h]
  rw [h_marg_eq]
  apply ENNReal.mul_inv_cancel
  · rw [h_marg_eq] at h_marg
    exact h_marg
  · exact ENNReal.mul_ne_top (apply_ne_top _ _) (apply_ne_top _ _)

/-- **Posterior order tracks kernel order at equal prior**: when
`μ a₁ = μ a₂` and the prior is positive there, the posterior ranks `a₁ <
a₂` exactly when the kernel does. Generalises both
"pragmatic strengthening with a uniform-equivalent prior" and
"threshold-posterior informativeness with a uniform threshold prior". -/
theorem posterior_lt_of_kernel_lt_of_prior_eq {α β : Type*}
    (κ : α → PMF β) (μ : PMF α) (b : β)
    (h_marg : marginal κ μ b ≠ 0) (a₁ a₂ : α)
    (h_prior_eq : μ a₁ = μ a₂) (h_prior_pos : μ a₁ ≠ 0)
    (h_kernel_lt : κ a₁ b < κ a₂ b) :
    posterior κ μ b h_marg a₁ < posterior κ μ b h_marg a₂ := by
  rw [posterior_lt_iff_score_lt, h_prior_eq]
  have h_prior_pos' : μ a₂ ≠ 0 := h_prior_eq ▸ h_prior_pos
  exact (ENNReal.mul_lt_mul_iff_right h_prior_pos' (apply_ne_top _ _)).mpr h_kernel_lt

end PMF
