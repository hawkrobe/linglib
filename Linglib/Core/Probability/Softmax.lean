import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Softmax distribution on PMFs

The **softmax distribution** at inverse temperature `β` over a finite,
nonempty type is the PMF with mass proportional to `exp(β · score)`:

  `softmax β score a ∝ exp(β · score a)`

Equivalently, this is the **Boltzmann distribution** / **Gibbs measure**
of statistical mechanics, and the uniform-prior case of mathlib's
`MeasureTheory.Measure.tilted` (the **exponentially tilted measure** /
**Esscher transform**). Pervasive in RSA-style pragmatics models for the
speaker step `S(u | w) ∝ exp(β · utility(u, w))`.

## Main definitions

* `PMF.softmax β score` — softmax PMF at inverse temperature `β`.

## Main statements

* `softmax_apply` — closed form.
* `softmax_pos` — every element has positive softmax mass.
* `softmax_lt_iff_score_lt` — the **structural-decomposition lemma**:
  comparing softmax values reduces to comparing scores (when `β > 0`).
  Foundation for "speaker prefers utterance u₂ over u₁" claims in RSA.
* `softmax_zero` / `softmax_const` — degenerate cases collapse to uniform.

## Connection to `MeasureTheory.Measure.tilted`

The general exponential-tilting construction is mathlib's
`Measure.tilted μ f := μ.withDensity (fun x ↦ ENNReal.ofReal
(exp (f x) / ∫ y, exp (f y) ∂μ))` over arbitrary base measures. The
softmax PMF is the uniform-prior case at the PMF level:

  `PMF.softmax β score = (PMF.uniformOfFintype α).tiltedBy (β · score)`

The non-uniform-prior generalisation (PMF-level Esscher transform) is
not yet defined here; add it when a consumer needs `prior · exp(score)`
shape that doesn't reduce to softmax.

## Architectural role

Substrate for RSA-style speaker constructions across `Phenomena/`:
@cite{frank-goodman-2012}, @cite{goodman-stuhlmuller-2013},
@cite{kao-etal-2014-metaphor}, @cite{lassiter-goodman-2017},
@cite{herbstritt-franke-2019}, @cite{yoon-etal-2020}, etc. Replaces
the per-paper inline `PMF.normalize ∘ exp ∘ score` pattern with a
named primitive backed by the structural-decomposition lemma.
-/

set_option autoImplicit false

open scoped ENNReal

namespace PMF

variable {α : Type*}

/-! ## Definition -/

/-- The unnormalised softmax weight at `a`: `exp(β · score a)`, lifted to
`ℝ≥0∞`. Convenient as a named unit for the apply formula and partition
function. -/
noncomputable def softmaxWeight (β : ℝ) (score : α → ℝ) (a : α) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (β * score a))

/-- Softmax weights are strictly positive. -/
theorem softmaxWeight_pos (β : ℝ) (score : α → ℝ) (a : α) :
    0 < softmaxWeight β score a :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- Softmax weights are non-zero. -/
theorem softmaxWeight_ne_zero (β : ℝ) (score : α → ℝ) (a : α) :
    softmaxWeight β score a ≠ 0 :=
  (softmaxWeight_pos β score a).ne'

/-- Softmax weights are finite. -/
theorem softmaxWeight_ne_top (β : ℝ) (score : α → ℝ) (a : α) :
    softmaxWeight β score a ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- **Softmax distribution** at inverse temperature `β`:
`softmax β score a ∝ exp(β · score a)`.

Inverse temperature `β` controls peakedness: `β = 0` gives uniform;
`β → ∞` concentrates on `argmax score`; `β < 0` inverts the preference
(selects `argmin`). Per RSA convention, this parameter is often called
`α` (the rationality parameter). For mathlib alignment we use `β`
(statistical-mechanics name).

For a finite, nonempty type, both `PMF.normalize` preconditions discharge
automatically: the partition function is a non-empty finite sum of
strictly positive terms (so non-zero) of finite values (so non-top). -/
noncomputable def softmax [Fintype α] [Nonempty α] (β : ℝ) (score : α → ℝ) :
    PMF α :=
  PMF.normalize (softmaxWeight β score)
    (by
      obtain ⟨a₀⟩ := ‹Nonempty α›
      exact ENNReal.summable.tsum_ne_zero_iff.mpr
        ⟨a₀, softmaxWeight_ne_zero β score a₀⟩)
    (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun a _ => softmaxWeight_ne_top β score a)

/-! ## Apply formula and basic API -/

/-- Closed form of the softmax value at `a`. -/
@[simp]
theorem softmax_apply [Fintype α] [Nonempty α]
    (β : ℝ) (score : α → ℝ) (a : α) :
    softmax β score a = softmaxWeight β score a / ∑ b, softmaxWeight β score b := by
  rw [softmax, PMF.normalize_apply, tsum_fintype, ENNReal.div_eq_inv_mul, mul_comm]

/-- The partition function `Z = ∑ b, exp(β · score b)` is non-zero. -/
theorem softmax_partition_ne_zero [Fintype α] [Nonempty α]
    (β : ℝ) (score : α → ℝ) :
    (∑ b, softmaxWeight β score b) ≠ 0 := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  intro h_sum
  exact softmaxWeight_ne_zero β score a₀
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le _) |>.mp h_sum a₀
      (Finset.mem_univ _))

/-- The partition function is finite. -/
theorem softmax_partition_ne_top [Fintype α] [Nonempty α]
    (β : ℝ) (score : α → ℝ) :
    (∑ b, softmaxWeight β score b) ≠ ∞ :=
  ENNReal.sum_ne_top.mpr fun a _ => softmaxWeight_ne_top β score a

/-- **Strict positivity**: every element has positive softmax mass. -/
theorem softmax_pos [Fintype α] [Nonempty α]
    (β : ℝ) (score : α → ℝ) (a : α) : 0 < softmax β score a := by
  rw [softmax_apply, ENNReal.div_pos_iff]
  exact ⟨softmaxWeight_ne_zero β score a, softmax_partition_ne_top β score⟩

/-- **The softmax support is everything** — a finite, nonempty type's softmax
distribution has full support. -/
@[simp]
theorem support_softmax [Fintype α] [Nonempty α]
    (β : ℝ) (score : α → ℝ) : (softmax β score).support = Set.univ := by
  ext a
  simp only [Set.mem_univ, iff_true, PMF.mem_support_iff]
  exact (softmax_pos β score a).ne'

/-! ## Comparison decomposition (RSA workhorse) -/

/-- **Comparison decomposition**: softmax preference reduces to comparing
unnormalised weights. The shared partition function `Z` cancels.

Foundation lemma for "speaker prefers utterance u₂ over u₁ at world w" claims
in RSA: the partition function depends on `w` but not on the utterance being
compared. -/
theorem softmax_lt_iff_weight_lt [Fintype α] [Nonempty α]
    (β : ℝ) (score : α → ℝ) (a₁ a₂ : α) :
    softmax β score a₁ < softmax β score a₂ ↔
      softmaxWeight β score a₁ < softmaxWeight β score a₂ := by
  rw [softmax_apply, softmax_apply]
  exact ENNReal.div_lt_div_iff_left
    (softmax_partition_ne_zero β score) (softmax_partition_ne_top β score)

/-- **Score comparison lifts to softmax comparison** at positive temperature.
The `β > 0` hypothesis is needed because negative temperature inverts
preference. -/
theorem softmax_lt_iff_score_lt [Fintype α] [Nonempty α]
    (β : ℝ) (hβ : 0 < β) (score : α → ℝ) (a₁ a₂ : α) :
    softmax β score a₁ < softmax β score a₂ ↔ score a₁ < score a₂ := by
  rw [softmax_lt_iff_weight_lt]
  unfold softmaxWeight
  rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_nonneg _),
      Real.exp_lt_exp]
  exact mul_lt_mul_iff_of_pos_left hβ

/-- **`≤` companion** of `softmax_lt_iff_score_lt`. -/
theorem softmax_le_iff_score_le [Fintype α] [Nonempty α]
    (β : ℝ) (hβ : 0 < β) (score : α → ℝ) (a₁ a₂ : α) :
    softmax β score a₁ ≤ softmax β score a₂ ↔ score a₁ ≤ score a₂ := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact softmax_lt_iff_score_lt β hβ score a₂ a₁

/-! ## Degenerate cases -/

/-- **Zero-temperature softmax is uniform**: with `β = 0`, softmax has no
preference signal. -/
theorem softmax_zero [Fintype α] [Nonempty α] (score : α → ℝ) :
    softmax 0 score = PMF.uniformOfFintype α := by
  ext a
  rw [softmax_apply, PMF.uniformOfFintype_apply]
  simp only [softmaxWeight, zero_mul, Real.exp_zero, ENNReal.ofReal_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      one_div]

/-- **Constant-score softmax is uniform**: a constant score gives no
preference signal. -/
theorem softmax_const [Fintype α] [Nonempty α] (β : ℝ) (c : ℝ) :
    softmax β (fun _ => c) = PMF.uniformOfFintype α := by
  ext a
  rw [softmax_apply, PMF.uniformOfFintype_apply]
  simp only [softmaxWeight]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Goal: E / (N * E) = N⁻¹.  Rewrite E = 1 * E, then mul_div_mul_right cancels.
  nth_rewrite 1 [show ENNReal.ofReal (Real.exp (β * c))
                      = 1 * ENNReal.ofReal (Real.exp (β * c)) from (one_mul _).symm]
  rw [ENNReal.mul_div_mul_right _ _
        (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top,
      one_div]

end PMF
