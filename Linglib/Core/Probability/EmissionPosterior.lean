import Linglib.Core.Probability.JointPosterior

/-!
# Emission posterior: inferring a partially observed joint action

For a kernel `κ : α → PMF (β × γ)` emitting a pair of which only the first
component is observed, `PMF.emissionPosterior κ μ b` is the Bayesian posterior
over `α × γ` — state together with unobserved component — given observation
`b`: the normalization of `(a, g) ↦ μ a · κ a (b, g)`.

This is the dual of `JointPosterior.lean`: there the *state* is a product and
the observation is total; here the *emission* is a product and the observation
is partial, which no `PMF`-valued kernel into `β` can express (the slice
`(a, g) ↦ κ a (b, g)` sums to the `γ`-marginal, not to `1`). At `γ := Unit`
the construction collapses to `PMF.posterior`.

## Main definitions

* `PMF.emissionPosterior` — posterior over `α × γ` from observing the first
  component of a jointly emitted pair.

## Main results

* `emissionPosterior_fst_lt_iff` / `emissionPosterior_snd_lt_iff` — marginal
  comparisons reduce to prior-weighted emission sums.
* `emissionPosterior_uniform_fst_lt_iff` / `_uniform_snd_lt_iff` — at a
  uniform prior, to bare emission sums.
-/

namespace PMF

open scoped ENNReal

variable {α β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β]

/-- The total score of an emission posterior is the observation marginal of
the `fst`-projected kernel. -/
theorem tsum_emission_score_eq (κ : α → PMF (β × γ)) (μ : PMF α) (b : β) :
    (∑' x : α × γ, μ x.1 * κ x.1 (b, x.2)) = marginal (fun a => (κ a).fst) μ b := by
  rw [ENNReal.tsum_prod']
  show (∑' a, ∑' g, μ a * κ a (b, g)) = (μ.bind fun a => (κ a).fst) b
  rw [PMF.bind_apply]
  exact tsum_congr fun a => by rw [ENNReal.tsum_mul_left, tsum_fintype, ← fst_apply]

/-- The conditional distribution over state and unobserved emission component
`(a, g)`, given that the kernel `κ` emitted a pair with observed first
component `b`. -/
noncomputable def emissionPosterior (κ : α → PMF (β × γ)) (μ : PMF α) (b : β)
    (h : marginal (fun a => (κ a).fst) μ b ≠ 0) : PMF (α × γ) :=
  PMF.normalize (fun x => μ x.1 * κ x.1 (b, x.2))
    (by rw [tsum_emission_score_eq]; exact h)
    (by rw [tsum_emission_score_eq]; exact marginal_ne_top _ μ b)

theorem emissionPosterior_apply (κ : α → PMF (β × γ)) (μ : PMF α) (b : β)
    (h : marginal (fun a => (κ a).fst) μ b ≠ 0) (x : α × γ) :
    emissionPosterior κ μ b h x
      = μ x.1 * κ x.1 (b, x.2) * (marginal (fun a => (κ a).fst) μ b)⁻¹ := by
  rw [emissionPosterior, PMF.normalize_apply, tsum_emission_score_eq]

/-- A single witness `(a, g)` with `μ a ≠ 0` and `κ a (b, g) ≠ 0` makes the
observation marginal non-zero. -/
theorem emission_marginal_ne_zero (κ : α → PMF (β × γ)) (μ : PMF α) {a : α} {b : β}
    {g : γ} (hμ : μ a ≠ 0) (hκ : κ a (b, g) ≠ 0) :
    marginal (fun a => (κ a).fst) μ b ≠ 0 :=
  marginal_ne_zero _ μ b hμ (fst_apply_ne_zero (x := (b, g)) hκ)

variable [Fintype α]

/-- Comparing state marginals of the emission posterior reduces to comparing
prior-weighted emission sums; the observation marginal cancels. -/
theorem emissionPosterior_fst_lt_iff [DecidableEq α] (κ : α → PMF (β × γ))
    (μ : PMF α) (b : β) (h : marginal (fun a => (κ a).fst) μ b ≠ 0) (a₁ a₂ : α) :
    (emissionPosterior κ μ b h).fst a₁ < (emissionPosterior κ μ b h).fst a₂
      ↔ (∑ g : γ, μ a₁ * κ a₁ (b, g)) < ∑ g : γ, μ a₂ * κ a₂ (b, g) := by
  rw [fst_apply, fst_apply]
  simp_rw [emissionPosterior_apply]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  exact ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr (marginal_ne_top _ μ b))
    (ENNReal.inv_ne_top.mpr h)

/-- Companion of `emissionPosterior_fst_lt_iff` for the unobserved component. -/
theorem emissionPosterior_snd_lt_iff [DecidableEq γ] (κ : α → PMF (β × γ))
    (μ : PMF α) (b : β) (h : marginal (fun a => (κ a).fst) μ b ≠ 0) (g₁ g₂ : γ) :
    (emissionPosterior κ μ b h).snd g₁ < (emissionPosterior κ μ b h).snd g₂
      ↔ (∑ a : α, μ a * κ a (b, g₁)) < ∑ a : α, μ a * κ a (b, g₂) := by
  rw [snd_apply, snd_apply]
  simp_rw [emissionPosterior_apply]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  exact ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr (marginal_ne_top _ μ b))
    (ENNReal.inv_ne_top.mpr h)

/-- At a uniform prior the prior cancels: state comparison reduces to bare
emission sums over the unobserved component. -/
theorem emissionPosterior_uniform_fst_lt_iff [DecidableEq α] [Nonempty α]
    (κ : α → PMF (β × γ)) (b : β)
    (h : marginal (fun a => (κ a).fst) (PMF.uniformOfFintype α) b ≠ 0) (a₁ a₂ : α) :
    (emissionPosterior κ (PMF.uniformOfFintype α) b h).fst a₁
        < (emissionPosterior κ (PMF.uniformOfFintype α) b h).fst a₂
      ↔ (∑ g : γ, κ a₁ (b, g)) < ∑ g : γ, κ a₂ (b, g) := by
  rw [emissionPosterior_fst_lt_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

/-- At a uniform prior the prior cancels: emission-component comparison reduces
to bare emission sums over states. -/
theorem emissionPosterior_uniform_snd_lt_iff [DecidableEq γ] [Nonempty α]
    (κ : α → PMF (β × γ)) (b : β)
    (h : marginal (fun a => (κ a).fst) (PMF.uniformOfFintype α) b ≠ 0) (g₁ g₂ : γ) :
    (emissionPosterior κ (PMF.uniformOfFintype α) b h).snd g₁
        < (emissionPosterior κ (PMF.uniformOfFintype α) b h).snd g₂
      ↔ (∑ a : α, κ a (b, g₁)) < ∑ a : α, κ a (b, g₂) := by
  rw [emissionPosterior_snd_lt_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

end PMF
