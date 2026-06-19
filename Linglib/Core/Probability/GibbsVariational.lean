import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The Gibbs / Donsker–Varadhan variational principle  [UPSTREAM]

For a probability measure `μ` and a function `f`, the **exponentially tilted
measure** `μ.tilted f` (`MeasureTheory.Measure.tilted`, the Gibbs measure /
Esscher transform with density `∝ exp f`) is the maximizer of the free-energy
functional `q ↦ 𝔼_q[f] − KL(q ‖ μ)`, and the maximal value is the **log-partition
function** `log ∫ exp f ∂μ`. This is the **Gibbs variational principle**
(a.k.a. **Donsker–Varadhan**), the variational characterization of the
Kullback–Leibler divergence anticipated by the module docstring of
`Mathlib/MeasureTheory/Measure/Tilted.lean`.

## Main definitions

* `MeasureTheory.Measure.logIntegralExp μ f = log (∫ x, exp (f x) ∂μ)` — the
  log-partition / free-energy functional. It is the cumulant generating function
  at unit argument (`logIntegralExp_eq_cgf : logIntegralExp μ f = cgf f μ 1`), and
  conversely `cgf X μ t = logIntegralExp μ (t • X)` (`logIntegralExp_const_mul`);
  the two are interchangeable, with `logIntegralExp` carrying the free-energy reading.

## Main statements

* `toReal_klDiv_tilted_right` — the **Gibbs decomposition identity** (finite `μ`):
  `KL(q ‖ μ.tilted f) = KL(q ‖ μ) − 𝔼_q[f] + logIntegralExp μ f + (1 − μ.real univ)`.
* `sub_klDiv_le_logIntegralExp` — the **variational inequality** (probability `μ`):
  `𝔼_q[f] − KL(q ‖ μ) ≤ logIntegralExp μ f` for all `q ≪ μ`.
* `sub_klDiv_tilted_eq_logIntegralExp` — the bound is **attained** at `μ.tilted f`.
* `isGreatest_logIntegralExp` — the **variational principle** in `IsGreatest` form:
  `logIntegralExp μ f` is the greatest value of `q ↦ 𝔼_q[f] − KL(q ‖ μ)`.

## Implementation notes

The decomposition reuses the log-likelihood-ratio identity
`MeasureTheory.integral_llr_tilted_right`. `μ.tilted f` is always a probability
measure, so `KL(q ‖ μ.tilted f)` collapses via `toReal_klDiv_of_measure_eq`; the
`KL(q ‖ μ)` term keeps its `toReal_klDiv` mass correction, giving the
`1 − μ.real univ` term — which vanishes for probability `μ`.

The decomposition is stated for a *finite, nonzero* prior `μ`; the variational
results specialize it to a *probability* `μ` (the clean Donsker–Varadhan form). The
*candidate* `q` is pinned to `[IsProbabilityMeasure]` by `integral_llr_tilted_right`
itself (it requires this on its left measure), so relaxing `q` is a separate
upstream concern in `LogLikelihoodRatio`, not here.
-/

open Real MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The **log-partition** (free-energy) functional `log ∫ exp f ∂μ`. It coincides
with the cumulant generating function `ProbabilityTheory.cgf` at unit argument
(`logIntegralExp_eq_cgf`), the free-energy reading being the one that makes the
variational principle below natural. -/
noncomputable def Measure.logIntegralExp (μ : Measure α) (f : α → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (f x) ∂μ)

/-- The log-partition functional is the cumulant generating function at unit
argument: `logIntegralExp μ f = cgf f μ 1`. -/
theorem logIntegralExp_eq_cgf (μ : Measure α) (f : α → ℝ) :
    μ.logIntegralExp f = cgf f μ 1 := by
  simp only [Measure.logIntegralExp, cgf, mgf, one_mul]

/-- The cumulant generating function is the log-partition functional of the scaled
integrand: `cgf X μ t = logIntegralExp μ (t • X)`. -/
theorem logIntegralExp_const_mul (μ : Measure α) (X : α → ℝ) (t : ℝ) :
    μ.logIntegralExp (fun x => t * X x) = cgf X μ t := by
  simp only [Measure.logIntegralExp, cgf, mgf]

/-- **Gibbs decomposition identity**: for a finite, nonzero reference measure `μ`
and a probability measure `q ≪ μ`, the Kullback–Leibler divergence from the Gibbs
measure `μ.tilted f` splits as
`KL(q ‖ μ.tilted f) = KL(q ‖ μ) − 𝔼_q[f] + logIntegralExp μ f + (1 − μ.real univ)`.
The `1 − μ.real univ` correction vanishes when `μ` is a probability measure, giving
the clean Donsker–Varadhan form used by the variational results below.

A `klDiv`-level repackaging of `integral_llr_tilted_right`: `μ.tilted f` is always a
probability measure (`isProbabilityMeasure_tilted`), so `KL(q ‖ μ.tilted f)`
collapses via `toReal_klDiv_of_measure_eq`; `KL(q ‖ μ)` keeps its `toReal_klDiv`
mass correction `μ.real univ − q.real univ`, the source (with `q.real univ = 1`) of
the `1 − μ.real univ` term. -/
theorem toReal_klDiv_tilted_right (μ q : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (klDiv q (μ.tilted f)).toReal
      = (klDiv q μ).toReal - (∫ x, f x ∂q) + μ.logIntegralExp f + (1 - μ.real Set.univ) := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have hq_tilt : q ≪ μ.tilted f := hqμ.trans (absolutelyContinuous_tilted h_exp)
  rw [toReal_klDiv_of_measure_eq hq_tilt (by simp only [measure_univ]),
      integral_llr_tilted_right hqμ h_int_f h_exp h_int_llr,
      toReal_klDiv hqμ h_int_llr, Measure.logIntegralExp]
  simp only [probReal_univ]
  ring

/-- **Gibbs / Donsker–Varadhan variational inequality**: for every probability
measure `q ≪ μ`, expected value minus relative entropy is bounded by the
log-partition function, `𝔼_q[f] − KL(q ‖ μ) ≤ logIntegralExp μ f`. Immediate from
the decomposition identity and `0 ≤ KL`. -/
theorem sub_klDiv_le_logIntegralExp (μ q : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure q] {f : α → ℝ} (hqμ : q ≪ μ)
    (h_int_llr : Integrable (llr q μ) q) (h_int_f : Integrable f q)
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (∫ x, f x ∂q) - (klDiv q μ).toReal ≤ μ.logIntegralExp f := by
  have h := toReal_klDiv_tilted_right μ q hqμ h_int_llr h_int_f h_exp
  have hnn : 0 ≤ (klDiv q (μ.tilted f)).toReal := ENNReal.toReal_nonneg
  have hμ : μ.real Set.univ = 1 := probReal_univ
  linarith

/-- The variational bound `sub_klDiv_le_logIntegralExp` is **attained** at the
Gibbs measure `μ.tilted f`: `𝔼_{μ.tilted f}[f] − KL(μ.tilted f ‖ μ) =
logIntegralExp μ f`. Immediate from the decomposition at `q = μ.tilted f`, where
the relative-entropy term `KL(μ.tilted f ‖ μ.tilted f)` vanishes. -/
theorem sub_klDiv_tilted_eq_logIntegralExp (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    (∫ x, f x ∂(μ.tilted f)) - (klDiv (μ.tilted f) μ).toReal = μ.logIntegralExp f := by
  have h_prob_tilt : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_exp
  have h := toReal_klDiv_tilted_right μ (μ.tilted f) (tilted_absolutelyContinuous μ f)
    h_int_llr h_int_f h_exp
  rw [klDiv_self, ENNReal.toReal_zero] at h
  have hμ : μ.real Set.univ = 1 := probReal_univ
  linarith

/-- **Gibbs / Donsker–Varadhan variational principle**: the log-partition
function `logIntegralExp μ f` is the *greatest* value of the free-energy
functional `q ↦ 𝔼_q[f] − KL(q ‖ μ)` over probability measures `q ≪ μ` (with the
relevant integrability), the maximum being attained at the Gibbs measure
`μ.tilted f`. Bundles `sub_klDiv_le_logIntegralExp` (upper bound) and
`sub_klDiv_tilted_eq_logIntegralExp` (attainment). -/
theorem isGreatest_logIntegralExp (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (h_int_f : Integrable f (μ.tilted f))
    (h_int_llr : Integrable (llr (μ.tilted f) μ) (μ.tilted f))
    (h_exp : Integrable (fun x => Real.exp (f x)) μ) :
    IsGreatest
      {x : ℝ | ∃ q : Measure α, IsProbabilityMeasure q ∧ q ≪ μ ∧
        Integrable (llr q μ) q ∧ Integrable f q ∧
        x = (∫ a, f a ∂q) - (klDiv q μ).toReal}
      (μ.logIntegralExp f) := by
  refine ⟨⟨μ.tilted f, isProbabilityMeasure_tilted h_exp, tilted_absolutelyContinuous μ f,
      h_int_llr, h_int_f, (sub_klDiv_tilted_eq_logIntegralExp μ h_int_f h_int_llr h_exp).symm⟩, ?_⟩
  rintro x ⟨q, hq_prob, hqμ, hq_llr, hq_f, rfl⟩
  haveI := hq_prob
  exact sub_klDiv_le_logIntegralExp μ q hqμ hq_llr hq_f h_exp

end MeasureTheory
