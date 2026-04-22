import Mathlib.Probability.ProbabilityMassFunction.Constructions
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

* `marginal_le_one`, `marginal_ne_top` — basic boundedness.
* `posterior_apply` — explicit Bayes formula.
* `posterior_apply_fintype` — Finset-sum form for `[Fintype α]`.

The bridge to `ProbabilityTheory.posterior` (via `PMF.toMeasure` /
`Measure.toKernel`) is left for a future file once a downstream
consumer needs the measure-theoretic identity.
-/

set_option autoImplicit false

namespace PMF

variable {α β : Type*}

open scoped ENNReal

/-- The marginal probability of observation `b` under the joint
distribution induced by kernel `κ` and prior `μ`:
`P(b) = ∑' a, μ a * κ a b`. -/
noncomputable def marginal (κ : α → PMF β) (μ : PMF α) (b : β) : ℝ≥0∞ :=
  ∑' a, μ a * κ a b

theorem marginal_le_one (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b ≤ 1 := by
  unfold marginal
  calc ∑' a, μ a * κ a b
      ≤ ∑' a, μ a := by
        refine ENNReal.tsum_le_tsum (fun a => ?_)
        calc μ a * κ a b ≤ μ a * 1 := mul_le_mul_left' (PMF.coe_le_one _ _) _
          _ = μ a := mul_one _
    _ = 1 := PMF.tsum_coe μ

theorem marginal_ne_top (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b ≠ ∞ :=
  (lt_of_le_of_lt (marginal_le_one κ μ b) ENNReal.one_lt_top).ne

/-- Bayesian posterior: for an observation `b`, the conditional
distribution over `α`. Well-defined when the marginal at `b` is
non-zero. The `≠ ∞` hypothesis required by `PMF.normalize` is supplied
automatically (the marginal is bounded above by `1`). -/
noncomputable def posterior (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) : PMF α :=
  PMF.normalize (fun a => μ a * κ a b) h (marginal_ne_top κ μ b)

theorem posterior_apply (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    posterior κ μ b h a = μ a * κ a b * (marginal κ μ b)⁻¹ :=
  PMF.normalize_apply _ _ a

/-- On a finite type the marginal is a `Finset.sum`. -/
theorem marginal_eq_sum [Fintype α] (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b = ∑ a, μ a * κ a b :=
  tsum_eq_sum (fun a (h : a ∉ Finset.univ) => absurd (Finset.mem_univ a) h)

/-- Finset-sum form of the posterior on a finite type. -/
theorem posterior_apply_fintype [Fintype α] (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    posterior κ μ b h a = μ a * κ a b * (∑ a', μ a' * κ a' b)⁻¹ := by
  rw [posterior_apply, marginal_eq_sum]

/-- The posterior is supported on the intersection of the prior's support
and the kernel's support at the observed `b`. -/
theorem mem_support_posterior_iff (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    a ∈ (posterior κ μ b h).support ↔ μ a ≠ 0 ∧ κ a b ≠ 0 := by
  rw [posterior, mem_support_normalize_iff]
  exact mul_ne_zero_iff

/-- Bayes' rule: the joint factors as marginal × posterior. -/
theorem marginal_mul_posterior_apply (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    marginal κ μ b * posterior κ μ b h a = μ a * κ a b := by
  rw [posterior_apply, ← mul_assoc, mul_comm (marginal κ μ b) (μ a * κ a b),
      mul_assoc, ENNReal.mul_inv_cancel h (marginal_ne_top κ μ b), mul_one]

end PMF
