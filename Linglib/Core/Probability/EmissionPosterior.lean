import Linglib.Core.Probability.JointPosterior

/-!
# Emission posterior: inferring a partially observed emission

For a kernel `κ : α → PMF β` whose emission is observed only through a map
`f : β → o`, `PMF.emissionPosterior f κ μ b` is the Bayesian posterior over
`α × β` — state together with the emission itself — given the observation `b`:
the normalization of `(a, x) ↦ μ a · κ a x` over the fibre `f x = b`. Observing
the first component of a pair-valued emission is the case `f := Prod.fst`, and
at `f := id` the state marginal is `PMF.posterior`.

This is the dual of `JointPosterior.lean`: there the *state* is a product and
the observation is total; here the emission is partially observed, which no
`PMF`-valued kernel into `o` can express (the fibre slice sums to the
`f`-marginal, not to `1`).

## Main definitions

* `PMF.emissionPosterior` — posterior over `α × β` from observing an emission
  through `f`.

## Main results

* `emissionPosterior_toOuterMeasure_lt_iff` — event comparisons reduce to
  prior-weighted emission sums over the observed fibre.
* `emissionPosterior_uniform_toOuterMeasure_lt_iff` — at a uniform prior, to
  bare fibre sums.
-/

namespace PMF

open scoped ENNReal

variable {α β o : Type*} (f : β → o) (κ : α → PMF β) (μ : PMF α) (b : o)

/-- A single witness `(a, x)` on the fibre with `μ a ≠ 0` and `κ a x ≠ 0` makes the
observation marginal non-zero. -/
theorem emission_marginal_ne_zero {a : α} {x : β} (hμ : μ a ≠ 0) (hκ : κ a x ≠ 0)
    (hx : f x = b) : marginal (fun a => (κ a).map f) μ b ≠ 0 :=
  marginal_ne_zero _ μ b hμ <| (PMF.mem_support_iff _ _).mp <|
    (PMF.mem_support_map_iff _ _ _).mpr ⟨x, (PMF.mem_support_iff _ _).mpr hκ, hx⟩

variable [DecidableEq o]

/-- The total score of an emission posterior is the observation marginal of the
`f`-pushed kernel. -/
theorem tsum_emission_score_eq :
    (∑' x : α × β, if f x.2 = b then μ x.1 * κ x.1 x.2 else 0)
      = marginal (fun a => (κ a).map f) μ b := by
  rw [ENNReal.tsum_prod']
  show _ = (μ.bind fun a => (κ a).map f) b
  rw [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  by_cases h : f x = b
  · simp [h]
  · simp [h, Ne.symm h]

/-- The conditional distribution over state and emission `(a, x)`, given that the
emission was observed as `b` through `f`. -/
noncomputable def emissionPosterior (h : marginal (fun a => (κ a).map f) μ b ≠ 0) :
    PMF (α × β) :=
  PMF.normalize (fun x => if f x.2 = b then μ x.1 * κ x.1 x.2 else 0)
    (by rw [tsum_emission_score_eq]; exact h)
    (by rw [tsum_emission_score_eq]; exact marginal_ne_top _ μ b)

theorem emissionPosterior_apply (h : marginal (fun a => (κ a).map f) μ b ≠ 0) (x : α × β) :
    emissionPosterior f κ μ b h x
      = (if f x.2 = b then μ x.1 * κ x.1 x.2 else 0)
          * (marginal (fun a => (κ a).map f) μ b)⁻¹ := by
  rw [emissionPosterior, PMF.normalize_apply, tsum_emission_score_eq]

/-- Comparing event masses of the emission posterior reduces to comparing
prior-weighted emission sums over the observed fibre; the observation marginal
cancels. -/
theorem emissionPosterior_toOuterMeasure_lt_iff (h : marginal (fun a => (κ a).map f) μ b ≠ 0)
    (E₁ E₂ : Finset (α × β)) :
    (emissionPosterior f κ μ b h).toOuterMeasure ↑E₁
        < (emissionPosterior f κ μ b h).toOuterMeasure ↑E₂
      ↔ (∑ x ∈ E₁ with f x.2 = b, μ x.1 * κ x.1 x.2)
          < ∑ x ∈ E₂ with f x.2 = b, μ x.1 * κ x.1 x.2 := by
  rw [PMF.toOuterMeasure_apply_finset, PMF.toOuterMeasure_apply_finset]
  simp_rw [emissionPosterior_apply]
  rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_filter, Finset.sum_filter]
  exact ENNReal.mul_lt_mul_iff_left
    (ENNReal.inv_ne_zero.mpr (marginal_ne_top _ μ b))
    (ENNReal.inv_ne_top.mpr h)

/-- At a uniform prior the prior cancels: event comparison reduces to bare
emission sums over the observed fibre. -/
theorem emissionPosterior_uniform_toOuterMeasure_lt_iff [Fintype α] [Nonempty α]
    (h : marginal (fun a => (κ a).map f) (PMF.uniformOfFintype α) b ≠ 0)
    (E₁ E₂ : Finset (α × β)) :
    (emissionPosterior f κ (PMF.uniformOfFintype α) b h).toOuterMeasure ↑E₁
        < (emissionPosterior f κ (PMF.uniformOfFintype α) b h).toOuterMeasure ↑E₂
      ↔ (∑ x ∈ E₁ with f x.2 = b, κ x.1 x.2) < ∑ x ∈ E₂ with f x.2 = b, κ x.1 x.2 := by
  rw [emissionPosterior_toOuterMeasure_lt_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

end PMF
