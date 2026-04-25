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

theorem marginal_le_one (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b ≤ 1 := by
  unfold marginal
  calc ∑' a, μ a * κ a b
      ≤ ∑' a, μ a := by
        refine ENNReal.tsum_le_tsum (fun a => ?_)
        calc μ a * κ a b ≤ μ a * 1 := mul_le_mul_right (PMF.coe_le_one _ _) _
          _ = μ a := mul_one _
    _ = 1 := PMF.tsum_coe μ

theorem marginal_ne_top (κ : α → PMF β) (μ : PMF α) (b : β) :
    marginal κ μ b ≠ ∞ :=
  (lt_of_le_of_lt (marginal_le_one κ μ b) ENNReal.one_lt_top).ne

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

@[simp]
theorem reweight_apply (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) (a : α) :
    p.reweight w h_pos h_fin a = p a * w a * (∑' x, p x * w x)⁻¹ :=
  PMF.normalize_apply _ _ _

theorem mem_support_reweight_iff (p : PMF α) (w : α → ℝ≥0∞)
    (h_pos : (∑' a, p a * w a) ≠ 0) (h_fin : (∑' a, p a * w a) ≠ ∞) (a : α) :
    a ∈ (p.reweight w h_pos h_fin).support ↔ p a ≠ 0 ∧ w a ≠ 0 := by
  rw [reweight, mem_support_normalize_iff]
  exact mul_ne_zero_iff

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
    a ∈ (posterior κ μ b h).support ↔ μ a ≠ 0 ∧ κ a b ≠ 0 :=
  mem_support_reweight_iff _ _ _ _ _

-- Product of Experts: combine two PMFs by pointwise product + renormalization

/-- Product of Experts: combine two PMFs over the same type by multiplying
mass at each point and renormalizing. Symmetric in `p`, `q`. The crucial
precondition (paper @cite{erk-herbelot-2024} fn 10): at least one point
must have non-zero mass under both factors. -/
noncomputable def productOfExperts (p q : PMF α)
    (h_pos : (∑' a, p a * q a) ≠ 0) : PMF α :=
  p.reweight (fun a => q a) h_pos
    (by
      apply ne_of_lt
      calc (∑' a, p a * q a)
          ≤ ∑' a, p a := ENNReal.tsum_le_tsum (fun a => by
            calc p a * q a ≤ p a * 1 := mul_le_mul_right (PMF.coe_le_one _ _) _
              _ = p a := mul_one _)
        _ = 1 := PMF.tsum_coe p
        _ < ∞ := ENNReal.one_lt_top)

@[simp]
theorem productOfExperts_apply (p q : PMF α) (h_pos : (∑' a, p a * q a) ≠ 0) (a : α) :
    p.productOfExperts q h_pos a = p a * q a * (∑' x, p x * q x)⁻¹ :=
  reweight_apply _ _ _ _ _

/-- PoE is commutative in the two factors (modulo the positivity hypothesis,
which is itself symmetric). -/
theorem productOfExperts_comm (p q : PMF α) (h : (∑' a, p a * q a) ≠ 0) :
    p.productOfExperts q h = q.productOfExperts p (by simpa [mul_comm] using h) := by
  ext a
  simp only [productOfExperts_apply, mul_comm (p a) (q a)]
  congr 1
  exact congr_arg _ (tsum_congr fun a => mul_comm _ _)

/-- PoE support: points with non-zero mass under both factors. The formal
content of @cite{erk-herbelot-2024} fn 10's caveat about disjoint supports. -/
theorem mem_support_productOfExperts_iff (p q : PMF α)
    (h : (∑' a, p a * q a) ≠ 0) (a : α) :
    a ∈ (p.productOfExperts q h).support ↔ p a ≠ 0 ∧ q a ≠ 0 :=
  mem_support_reweight_iff _ _ _ _ _

/-- Bayes' rule: the joint factors as marginal × posterior. -/
theorem marginal_mul_posterior_apply (κ : α → PMF β) (μ : PMF α) (b : β)
    (h : marginal κ μ b ≠ 0) (a : α) :
    marginal κ μ b * posterior κ μ b h a = μ a * κ a b := by
  rw [posterior_apply, ← mul_assoc, mul_comm (marginal κ μ b) (μ a * κ a b),
      mul_assoc, ENNReal.mul_inv_cancel h (marginal_ne_top κ μ b), mul_one]

end PMF
