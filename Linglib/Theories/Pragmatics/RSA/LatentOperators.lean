import Linglib.Theories.Pragmatics.RSA.Operators

/-!
# RSA — Latent-aware unbundled operators
@cite{lassiter-goodman-2017} @cite{kao-etal-2014-hyperbole} @cite{nouwen-2024}

Latent-variable extensions to the unbundled `Operators.lean` API. RSA models
with latent variables (thresholds, QUDs, lexicons) parameterize their L0/S1
on a latent type `L`; the L1 marginalizes over `L` against a latent prior.

The audit in `project_rsa_v2_functional.md` flagged that **87% of RSAConfig
consumers use Latent ≠ Unit** — so latent support must be first-class in any
unbundled v2 API, not an afterthought.

## Operators

* `L0LassiterGoodman` — L&G L0 with prior baked in: `P.reweight meaning`. The
  paper-name alias for the standard `PMF.reweight` operation specialized to
  the L&G "prior in literal listener" pattern (eq 70/71 of @cite{lassiter-goodman-2017}).
* `marginalizeKernel` — marginalize a latent-parameterized kernel against
  a latent prior. Just `PMF.bind` of the latent prior into the kernel slice
  at each world. This is the operator that turns a `Latent → W → PMF U`
  family into a single `W → PMF U` for use as the speaker in `L1`.

(Latent-parameterized `*Latent` wrappers and `composeStages` were deleted
in 0.230.373 — they added no operator content over partial application
or function composition. See HISTORY at end.)

## L&G "two priors" pattern

For the L&G family (used by @cite{lassiter-goodman-2017},
@cite{nouwen-2024}, intensifier studies), the same prior `P` enters BOTH:
- L0 via `P.reweight meaning` (the literal listener is Bayesian with prior `P`)
- L1 via `PMF.posterior speaker P` (the pragmatic listener is Bayesian with prior `P`)

This double-occurrence is faithful to the paper specification, not
double-counting. With this file's operators, the pattern is straightforward:
construct L0 via `L0LassiterGoodman P meaning`, build the speaker on top,
then close with `PMF.posterior speaker P`. The same `P` shows up in both
function calls — the structure makes it explicit.

## Sequential composition

Sequential between-stage composition (Nouwen 2024 eq 73: Π = stage 1's L1
becomes stage 2's prior) is just function composition: pass the previous
stage's `PMF.posterior` output as the prior argument to the next stage's
construction. No new operator needed — the existing PMF infrastructure is
sufficient.

The `composeStages` helper below is a thin alias documenting this idiom.

## Relationship to Phase 5 migration

This file is part of Phase 1.5 of the RSA → mathlib-PMF migration
(`project_rsa_pmf_migration.md`). It extends the unbundled operator suite
to cover the latent and L&G patterns identified in the consumer audit
(6 canonical patterns, 47 files). Phase 5 study migrations build on these.

A Nouwen2024PMF pilot demonstrating the L&G two-prior + latent + sequential
pattern end-to-end is the natural next step — see commented sketch in
`L0LassiterGoodman` and `marginalizeKernel` docstrings for how to use them.
-/

set_option autoImplicit false

open scoped ENNReal

namespace RSA

variable {U W L : Type*}

/-! ## L0 with L&G "prior in literal listener" pattern -/

/-- Lassiter-Goodman literal listener (eq 71 of @cite{lassiter-goodman-2017}):
the prior `P` is part of the literal listener's Bayesian update. For a
Boolean-valued meaning function `meaning : U → W → Bool`, this returns
`P` reweighted by the indicator function of the meaning's extension.

Mathematically:
  `L0_LG(w | u) = P(w) · ⟦u⟧(w) / Σ_{w'} P(w') · ⟦u⟧(w')`

This is exactly `PMF.reweight P (fun w => indicator (meaning u w))`. -/
noncomputable def L0LassiterGoodman (P : PMF W) (meaning : U → W → Bool) (u : U)
    (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0) : PMF W :=
  P.reweight (fun w => if meaning u w then 1 else 0) h_pos
    (by
      apply ne_of_lt
      calc (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0))
          ≤ ∑' w, P w := ENNReal.tsum_le_tsum (fun w => by
            split <;> simp)
        _ = 1 := PMF.tsum_coe P
        _ < ∞ := ENNReal.one_lt_top)

-- Not `@[simp]`: introduces `(∑' w', ...)⁻¹`; use explicitly via `rw`.
theorem L0LassiterGoodman_apply (P : PMF W) (meaning : U → W → Bool) (u : U)
    (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0) (w : W) :
    L0LassiterGoodman P meaning u h_pos w =
      P w * (if meaning u w then 1 else 0) *
        (∑' w', P w' * (if meaning u w' then (1 : ℝ≥0∞) else 0))⁻¹ :=
  PMF.reweight_apply _ _ _ _ _

theorem mem_support_L0LassiterGoodman_iff (P : PMF W) (meaning : U → W → Bool) (u : U)
    (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0) (w : W) :
    w ∈ (L0LassiterGoodman P meaning u h_pos).support ↔ P w ≠ 0 ∧ meaning u w = true := by
  rw [L0LassiterGoodman, PMF.mem_support_reweight_iff]
  refine and_congr Iff.rfl ?_
  by_cases h : meaning u w = true <;> simp [h]

/-- **Vacuous-utterance reduction**: when `meaning u` is identically true
(e.g. `.silent`), the L&G L0 at `u` reduces to the prior unchanged.

This is the building block for many positivity discharges in consumer code:
"the silent utterance has L0 = prior (positive everywhere by assumption),
so its contribution to any normalization sum is non-zero." -/
theorem L0LassiterGoodman_apply_of_meaning_true (P : PMF W) (meaning : U → W → Bool)
    (u : U) (h_meaning : ∀ w, meaning u w = true)
    (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0) (w : W) :
    L0LassiterGoodman P meaning u h_pos w = P w := by
  rw [L0LassiterGoodman_apply]
  -- Each (if meaning u w then 1 else 0) reduces to 1.
  have h_indic : ∀ w', (if meaning u w' then (1 : ℝ≥0∞) else 0) = 1 := fun w' => by
    rw [h_meaning w']; rfl
  rw [h_indic w]
  -- Sum simplifies to P.tsum = 1; inverse is 1.
  have h_sum : (∑' w', P w' * (if meaning u w' then (1 : ℝ≥0∞) else 0)) = 1 := by
    simp only [h_indic, mul_one]
    exact PMF.tsum_coe P
  rw [h_sum, mul_one, inv_one, mul_one]

/-- **Inequality decomposition for L&G L0**: at a fixed utterance, comparing
two worlds' literal-listener probabilities reduces to comparing their
unnormalised scores `P(w) · indicator(meaning u w)`. The partition function
`Z(u)` depends on the utterance but not the world, so it cancels.

Direct lift from `PMF.reweight_lt_iff_lt`. -/
theorem L0LassiterGoodman_apply_lt_iff (P : PMF W) (meaning : U → W → Bool)
    (u : U) (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0)
    (w₁ w₂ : W) :
    L0LassiterGoodman P meaning u h_pos w₁ < L0LassiterGoodman P meaning u h_pos w₂ ↔
      P w₁ * (if meaning u w₁ then (1 : ℝ≥0∞) else 0) <
        P w₂ * (if meaning u w₂ then (1 : ℝ≥0∞) else 0) :=
  PMF.reweight_lt_iff_lt _ _ _ _ _ _

/-- The `≤` companion of `L0LassiterGoodman_apply_lt_iff`. -/
theorem L0LassiterGoodman_apply_le_iff (P : PMF W) (meaning : U → W → Bool)
    (u : U) (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0)
    (w₁ w₂ : W) :
    L0LassiterGoodman P meaning u h_pos w₁ ≤ L0LassiterGoodman P meaning u h_pos w₂ ↔
      P w₁ * (if meaning u w₁ then (1 : ℝ≥0∞) else 0) ≤
        P w₂ * (if meaning u w₂ then (1 : ℝ≥0∞) else 0) :=
  PMF.reweight_le_iff_le _ _ _ _ _ _

/-- **Convenience corollary**: when the utterance's meaning is true at both
worlds, the L0 comparison collapses to a prior comparison. The indicator is
1 on both sides, the partition function cancels — only `P(w)` is left. -/
theorem L0LassiterGoodman_apply_lt_iff_prior_lt (P : PMF W) (meaning : U → W → Bool)
    (u : U) (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0)
    (w₁ w₂ : W) (h₁ : meaning u w₁ = true) (h₂ : meaning u w₂ = true) :
    L0LassiterGoodman P meaning u h_pos w₁ < L0LassiterGoodman P meaning u h_pos w₂ ↔
      P w₁ < P w₂ := by
  rw [L0LassiterGoodman_apply_lt_iff, h₁, h₂]
  simp only [if_true, mul_one]

/-- The `≤` companion of `L0LassiterGoodman_apply_lt_iff_prior_lt`. -/
theorem L0LassiterGoodman_apply_le_iff_prior_le (P : PMF W) (meaning : U → W → Bool)
    (u : U) (h_pos : (∑' w, P w * (if meaning u w then (1 : ℝ≥0∞) else 0)) ≠ 0)
    (w₁ w₂ : W) (h₁ : meaning u w₁ = true) (h₂ : meaning u w₂ = true) :
    L0LassiterGoodman P meaning u h_pos w₁ ≤ L0LassiterGoodman P meaning u h_pos w₂ ↔
      P w₁ ≤ P w₂ := by
  rw [L0LassiterGoodman_apply_le_iff, h₁, h₂]
  simp only [if_true, mul_one]

/-! ## Marginalization over latents

The latent-parameterized "wrappers" `L0OfMeaningLatent`, `L0LassiterGoodmanLatent`,
`S1BeliefLatent` were deleted in 0.230.373 (mathlib hygiene audit). They added
no operator content over partial application: e.g.
`L0OfMeaningLatent meaning l u h0 hTop` was just `L0OfMeaning (meaning l) u h0 hTop`.
Mathlib doesn't define `Function.compLatent`. Consumers should write the partial
application directly. -/

/-- Marginalize a latent-parameterized kernel against a latent prior:
`marginalize prior κ a = ∑_l prior(l) · κ(l, a)` as a PMF over `β`.

This is `PMF.bind` of the latent prior into the kernel slice at each `a`.
The operator that turns a `L → α → PMF β` family into a single `α → PMF β`
suitable for use as the speaker kernel in `L1 = PMF.posterior`.

For Nouwen2024-style models where the latent is a Threshold marginalized
in L1, the typical pattern is:
```
def speakerLatent : Threshold → Height → PMF EvalUtterance := S1BeliefLatent ...
def marginalizedSpeaker : Height → PMF EvalUtterance :=
  marginalizeKernel (PMF.uniformOfFintype Threshold) speakerLatent
def L1 : EvalUtterance → PMF Height :=
  fun u => PMF.posterior marginalizedSpeaker heightPrior u (h_marginal_ne_zero u)
```
-/
noncomputable def marginalizeKernel {α β : Type*}
    (latentPrior : PMF L) (κ : L → α → PMF β) (a : α) : PMF β :=
  PMF.bind latentPrior (fun l => κ l a)

@[simp] theorem marginalizeKernel_apply {α β : Type*}
    (latentPrior : PMF L) (κ : L → α → PMF β) (a : α) (b : β) :
    marginalizeKernel latentPrior κ a b = ∑' l, latentPrior l * κ l a b := by
  unfold marginalizeKernel
  rw [PMF.bind_apply]

theorem mem_support_marginalizeKernel_iff {α β : Type*}
    (latentPrior : PMF L) (κ : L → α → PMF β) (a : α) (b : β) :
    b ∈ (marginalizeKernel latentPrior κ a).support ↔
      ∃ l, latentPrior l ≠ 0 ∧ b ∈ (κ l a).support := by
  unfold marginalizeKernel
  rw [PMF.mem_support_bind_iff]
  simp only [PMF.mem_support_iff]

/-- **Inequality decomposition for `marginalizeKernel`** (cross-`a`, same `b`):
when the kernel slice at `a₂` dominates the slice at `a₁` pointwise — and is
strict at some latent `l₀` with positive prior mass — the marginalized kernel
inherits the strict inequality.

Direct lift of `PMF.marginal_lt_marginal` after unfolding `bind_apply`.

Use case: "the marginalized speaker assigns higher probability to utterance `u`
at world `w₂` than at world `w₁`" reduces to "for every latent threshold, the
per-latent speaker prefers `u` at `w₂`, with strict preference at some
threshold." -/
theorem marginalizeKernel_lt_marginalizeKernel {α β : Type*}
    (μ : PMF L) (κ : L → α → PMF β) (b : β)
    {a₁ a₂ : α} {l₀ : L} (hμ : μ l₀ ≠ 0)
    (h : ∀ l, κ l a₁ b ≤ κ l a₂ b)
    (hi : κ l₀ a₁ b < κ l₀ a₂ b) :
    marginalizeKernel μ κ a₁ b < marginalizeKernel μ κ a₂ b := by
  rw [marginalizeKernel_apply, marginalizeKernel_apply]
  exact PMF.marginal_lt_marginal (κ₁ := fun l => κ l a₁) (κ₂ := fun l => κ l a₂)
    hμ h hi

/-- The `≤` companion of `marginalizeKernel_lt_marginalizeKernel`. -/
theorem marginalizeKernel_le_marginalizeKernel {α β : Type*}
    (μ : PMF L) (κ : L → α → PMF β) (b : β)
    {a₁ a₂ : α} (h : ∀ l, κ l a₁ b ≤ κ l a₂ b) :
    marginalizeKernel μ κ a₁ b ≤ marginalizeKernel μ κ a₂ b := by
  rw [marginalizeKernel_apply, marginalizeKernel_apply]
  exact PMF.marginal_le_marginal (κ₁ := fun l => κ l a₁) (κ₂ := fun l => κ l a₂) h

/-! ## Sequential between-stage composition (Nouwen eq 73)

Two successive ρ updates, where stage 2's prior is stage 1's L1 output at
a specific stage-1 utterance. This is just function composition — pass the
previous-stage L1 as the prior argument to the next stage's L1 construction.

For example, given:
* `evalL1 : EvalUtterance → PMF Height` — stage 1 L1
* `adjL1Builder : PMF Height → AdjUtterance → PMF Height` — stage 2 L1
  parameterized by its prior

The sequential L1 at the specific stage-1 observation `u_eval = .eval_pos` is:
  `seqAdjL1 u₂ := adjL1Builder (evalL1 .eval_pos) u₂`

No operator needed. (The `composeStages` alias was deleted in 0.230.373 —
function-application doesn't need a name.) -/

end RSA
