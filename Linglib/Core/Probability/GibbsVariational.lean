import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The Gibbs / Donsker–Varadhan variational principle  [UPSTREAM]

For a probability measure `μ` and a function `f`, the **free energy**
`q ↦ 𝔼_q[f] − KL(q ‖ μ)` is maximized over probability measures `q ≪ μ` by the
exponentially tilted (Gibbs) measure `μ.tilted f`, the maximal value being the
cumulant generating function `cgf f μ 1 = log ∫ exp f ∂μ`. This is the **Gibbs
variational principle** (a.k.a. **Donsker–Varadhan**), the variational
characterization of the Kullback–Leibler divergence whose existence is anticipated
by the module docstring of `Mathlib/MeasureTheory/Measure/Tilted.lean`.

## Main definitions

* `MeasureTheory.Measure.freeEnergy μ f q = 𝔼_q[f] − (klDiv q μ).toReal` — the
  free-energy functional whose greatest value is the variational principle's value.

## Main statements

* `InformationTheory.toReal_klDiv_tilted_right` — the **Gibbs decomposition
  identity**: `KL(q ‖ μ.tilted f) = KL(q ‖ μ) − 𝔼_q[f] + cgf f μ 1`.
* `InformationTheory.freeEnergy_le_cgf` — the **variational inequality**:
  `freeEnergy μ f q ≤ cgf f μ 1` for every probability measure `q ≪ μ`.
* `InformationTheory.freeEnergy_tilted` — the bound is **attained** at `μ.tilted f`.
* `InformationTheory.isGreatest_cgf` — the **variational principle**: `cgf f μ 1` is
  the greatest value of `freeEnergy μ f` over admissible `q`.

## Implementation notes

The decomposition repackages `MeasureTheory.integral_llr_tilted_right` at the
`klDiv` level: `μ.tilted f` is a probability measure, so both `klDiv` terms collapse
to their `llr`-integrals via `toReal_klDiv_of_measure_eq`. The value is the cumulant
generating function `cgf f μ 1` (= `log ∫ exp f ∂μ`), connecting the principle to the
`Probability/Moments` API. The candidate `q` is pinned to `[IsProbabilityMeasure]`
by `integral_llr_tilted_right` (which requires it on its left measure), so relaxing
it is a separate upstream concern in `LogLikelihoodRatio`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The **free-energy functional** `𝔼_q[f] − KL(q ‖ μ)`, whose greatest value over
probability measures `q ≪ μ` is the Gibbs / Donsker–Varadhan variational principle. -/
noncomputable def Measure.freeEnergy (μ : Measure α) (f : α → ℝ) (q : Measure α) : ℝ :=
  (∫ a, f a ∂q) - (klDiv q μ).toReal

end MeasureTheory

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Gibbs decomposition identity**: for probability measures `q ≪ μ`, the
Kullback–Leibler divergence from the Gibbs measure `μ.tilted f` splits as
`KL(q ‖ μ.tilted f) = KL(q ‖ μ) − 𝔼_q[f] + cgf f μ 1`.

A `klDiv`-level repackaging of `integral_llr_tilted_right`: `μ.tilted f` is a
probability measure, so both divergences collapse to their `llr`-integrals via
`toReal_klDiv_of_measure_eq`, after which the log-likelihood-ratio decomposition
closes it (the value being `cgf f μ 1 = log ∫ exp f ∂μ`). -/
theorem toReal_klDiv_tilted_right (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (klDiv q (μ.tilted f)).toReal = (klDiv q μ).toReal - (∫ x, f x ∂q) + cgf f μ 1 := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have hq_tilt : q ≪ μ.tilted f := hqμ.trans (absolutelyContinuous_tilted h_exp)
  rw [toReal_klDiv_of_measure_eq hq_tilt (by simp only [measure_univ]),
      toReal_klDiv_of_measure_eq hqμ (by simp only [measure_univ]),
      integral_llr_tilted_right hqμ h_int_f h_exp h_int_llr]
  simp only [cgf, mgf, one_mul]

/-- **Gibbs / Donsker–Varadhan variational inequality**: for every probability
measure `q ≪ μ`, the free energy is bounded by the cumulant generating function,
`freeEnergy μ f q ≤ cgf f μ 1`. Immediate from the decomposition identity and
`0 ≤ KL`. -/
theorem freeEnergy_le_cgf (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    μ.freeEnergy f q ≤ cgf f μ 1 := by
  have h := toReal_klDiv_tilted_right μ q hqμ h_int_llr h_int_f h_exp
  have hnn : 0 ≤ (klDiv q (μ.tilted f)).toReal := ENNReal.toReal_nonneg
  rw [Measure.freeEnergy]
  linarith

/-- The variational bound `freeEnergy_le_cgf` is **attained** at the Gibbs measure
`μ.tilted f`: `freeEnergy μ f (μ.tilted f) = cgf f μ 1`. Immediate from the
decomposition at `q = μ.tilted f`, where `KL(μ.tilted f ‖ μ.tilted f)` vanishes. -/
theorem freeEnergy_tilted (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    μ.freeEnergy f (μ.tilted f) = cgf f μ 1 := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have h := toReal_klDiv_tilted_right μ (μ.tilted f) (tilted_absolutelyContinuous μ f)
    h_int_llr h_int_f h_exp
  rw [klDiv_self, ENNReal.toReal_zero] at h
  rw [Measure.freeEnergy]
  linarith

/-- **Gibbs / Donsker–Varadhan variational principle**: the cumulant generating
function `cgf f μ 1` is the *greatest* value of the free-energy functional
`freeEnergy μ f` over probability measures `q ≪ μ` (with the relevant
integrability), the maximum being attained at the Gibbs measure `μ.tilted f`.
Bundles `freeEnergy_le_cgf` (upper bound) and `freeEnergy_tilted` (attainment). -/
theorem isGreatest_cgf (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    IsGreatest (μ.freeEnergy f '' {q | IsProbabilityMeasure q ∧ q ≪ μ ∧
        Integrable (llr q μ) q ∧ Integrable f q}) (cgf f μ 1) := by
  refine ⟨⟨μ.tilted f, ⟨isProbabilityMeasure_tilted h_exp, tilted_absolutelyContinuous μ f,
      h_int_llr, h_int_f⟩, freeEnergy_tilted μ h_int_f h_int_llr h_exp⟩, ?_⟩
  rintro x ⟨q, ⟨hq_prob, hqμ, hq_llr, hq_f⟩, rfl⟩
  exact freeEnergy_le_cgf μ q hqμ hq_llr hq_f h_exp

end InformationTheory
