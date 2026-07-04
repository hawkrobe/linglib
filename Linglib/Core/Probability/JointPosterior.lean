import Linglib.Core.Probability.Posterior
import Linglib.Core.Probability.Marginal

/-!
# Joint posterior reasoning: posterior over `α × β`

Theorems about `PMF.posterior` instantiated at product types `α × β`, and
how marginalization (`PMF.fst` / `PMF.snd`) interacts with the resulting
joint posterior.

The "joint posterior" is just `PMF.posterior` at `α := γ × δ` — **no new
definition is introduced**. This file collects the structural theorems
for working with such posteriors:

* `posterior_fst_apply` — closed form for the first-marginalized joint
  posterior (Bayes + marginalization). Used for L&G2017 Eq. 30 (height
  marginalization of the joint world × threshold posterior).
* `posterior_fst_lt_iff` — inequality decomposition for the marginalized
  form. Generalizes `posterior_lt_iff_score_lt` to the marginalized case.

## Use cases

- [lassiter-goodman-2017] Eq. 30: height marginalization of the
  joint `(world × threshold)` posterior gives the world posterior.
- [kao-etal-2014-metaphor]: world marginalization of the joint
  `(world × QUD)` posterior.
- General latent-variable RSA where the listener jointly infers
  `(state, latent)` and the per-state marginal posterior is wanted.

## Architectural role

This file is part of the **structural track** of the PMF-based RSA
discipline (cf. `Pragmatics/RSA/Cancellation.lean`). The
structural-track substrate provides theorems about model-class behavior
(joint inference, marginalization, cancellation); per-paper studies
build on it via instantiations and `example`-style illustrations.
-/

namespace PMF

variable {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- **Closed form for the first-marginalized joint posterior**.

For a likelihood `κ : (α × β) → PMF γ` and a joint prior `joint : PMF (α × β)`,
the first-component marginal of the joint posterior at observation `c` is

  `(posterior κ joint c).fst a = (∑_b joint(a, b) · κ(a, b)(c)) / marginal κ joint c`

Direct combination of `posterior_apply` (Bayes' rule) and `fst_apply`
(marginal-from-joint as row-sum). The numerator is the **conditional
joint mass for first-component `a`** integrated over the second component.

This is the L&G2017 Eq. 30 pattern: marginalize the joint `(world, threshold)`
posterior over thresholds to get the per-world posterior. Same shape, different
domain interpretation. -/
theorem posterior_fst_apply
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (a : α) :
    (posterior κ joint c h).fst a
      = (∑ b : β, joint (a, b) * κ (a, b) c) / marginal κ joint c := by
  rw [fst_apply]
  -- ∑ b : β, posterior κ joint c h (a, b)
  --   = ∑ b : β, joint (a, b) * κ (a, b) c * (marginal κ joint c)⁻¹  -- by posterior_apply
  --   = (∑ b : β, joint (a, b) * κ (a, b) c) * (marginal κ joint c)⁻¹  -- factor out
  --   = (...) / marginal κ joint c                                      -- div = mul_inv
  simp_rw [posterior_apply]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]

/-- **Comparison decomposition for the first-marginalized joint posterior**.

Comparing two marginalized joint posteriors at first-components `a₁` and `a₂`
reduces to comparing the corresponding conditional-joint sums. The shared
denominator `marginal κ joint c` cancels.

Generalizes `posterior_lt_iff_score_lt` to the marginalized-product case:
`posterior_lt_iff_score_lt` compares per-element scores `μ a · κ a b`;
this compares per-first-component conditional sums
`∑_b joint(a, b) · κ(a, b)(c)`. -/
theorem posterior_fst_lt_iff
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (a₁ a₂ : α) :
    (posterior κ joint c h).fst a₁ < (posterior κ joint c h).fst a₂
      ↔ (∑ b : β, joint (a₁, b) * κ (a₁, b) c)
          < ∑ b : β, joint (a₂, b) * κ (a₂, b) c := by
  rw [posterior_fst_apply, posterior_fst_apply]
  -- Both sides are `(...) / marginal κ joint c`. Shared denominator cancels via div_lt_div_iff_left.
  exact ENNReal.div_lt_div_iff_left h (marginal_ne_top κ joint c)

/-- **Companion `≤` form** of `posterior_fst_lt_iff`. -/
theorem posterior_fst_le_iff
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (a₁ a₂ : α) :
    (posterior κ joint c h).fst a₁ ≤ (posterior κ joint c h).fst a₂
      ↔ (∑ b : β, joint (a₁, b) * κ (a₁, b) c)
          ≤ ∑ b : β, joint (a₂, b) * κ (a₂, b) c := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact posterior_fst_lt_iff κ joint c h a₂ a₁

/-- **Companion `=` form** of `posterior_fst_lt_iff`: conditional-joint-sum symmetry. -/
theorem posterior_fst_eq_iff
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (a₁ a₂ : α) :
    (posterior κ joint c h).fst a₁ = (posterior κ joint c h).fst a₂
      ↔ (∑ b : β, joint (a₁, b) * κ (a₁, b) c)
          = ∑ b : β, joint (a₂, b) * κ (a₂, b) c := by
  simp only [le_antisymm_iff, posterior_fst_le_iff]

omit [DecidableEq α] in
/-- **Closed form for the second-marginalized joint posterior**.
Companion of `posterior_fst_apply` for the second component. Used by
L&G2017 for the threshold-marginal posterior `P_L1(θ | u)` (Fig. 5 left
panel) — analogous to the world-marginal `P_L1(h | u)` from `posterior_fst_apply`. -/
theorem posterior_snd_apply [DecidableEq β]
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (b : β) :
    (posterior κ joint c h).snd b
      = (∑ a : α, joint (a, b) * κ (a, b) c) / marginal κ joint c := by
  rw [snd_apply]
  simp_rw [posterior_apply]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]

omit [DecidableEq α] in
/-- **Comparison decomposition for the second-marginalized joint posterior**.
Companion of `posterior_fst_lt_iff`. -/
theorem posterior_snd_lt_iff [DecidableEq β]
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (b₁ b₂ : β) :
    (posterior κ joint c h).snd b₁ < (posterior κ joint c h).snd b₂
      ↔ (∑ a : α, joint (a, b₁) * κ (a, b₁) c)
          < ∑ a : α, joint (a, b₂) * κ (a, b₂) c := by
  rw [posterior_snd_apply, posterior_snd_apply]
  exact ENNReal.div_lt_div_iff_left h (marginal_ne_top κ joint c)

omit [DecidableEq α] in
/-- **Companion `≤` form** of `posterior_snd_lt_iff`. -/
theorem posterior_snd_le_iff [DecidableEq β]
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (b₁ b₂ : β) :
    (posterior κ joint c h).snd b₁ ≤ (posterior κ joint c h).snd b₂
      ↔ (∑ a : α, joint (a, b₁) * κ (a, b₁) c)
          ≤ ∑ a : α, joint (a, b₂) * κ (a, b₂) c := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact posterior_snd_lt_iff κ joint c h b₂ b₁

omit [DecidableEq α] in
/-- **Companion `=` form** of `posterior_snd_lt_iff`: conditional-joint-sum symmetry. -/
theorem posterior_snd_eq_iff [DecidableEq β]
    (κ : (α × β) → PMF γ) (joint : PMF (α × β)) (c : γ)
    (h : marginal κ joint c ≠ 0) (b₁ b₂ : β) :
    (posterior κ joint c h).snd b₁ = (posterior κ joint c h).snd b₂
      ↔ (∑ a : α, joint (a, b₁) * κ (a, b₁) c)
          = ∑ a : α, joint (a, b₂) * κ (a, b₂) c := by
  simp only [le_antisymm_iff, posterior_snd_le_iff]

end PMF
