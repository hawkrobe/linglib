/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Regularity of the cdf of a real probability measure

Each regularity property of `ProbabilityTheory.cdf μ` is the image of a property of `μ`. The cdf is
continuous at the points that are not atoms, strictly monotone when `μ` charges every nonempty open
set, and satisfies the reflection formula `cdf μ (-x) = 1 - cdf μ x` when `μ` is invariant under
negation. A measure with the first two properties has a cdf that is an order isomorphism from `ℝ`
onto `(0, 1)`, whose inverse is the quantile function. `[UPSTREAM]` candidate for
`Mathlib/Probability/CDF.lean`.

## Main definitions

* `ProbabilityTheory.cdfOrderIso`: the cdf as an order isomorphism `ℝ ≃o Ioo 0 1`.

## Main results

* `ProbabilityTheory.continuousAt_cdf_iff`: the cdf is continuous at `x` iff `μ {x} = 0`.
* `ProbabilityTheory.strictMono_cdf`: the cdf of an open-positive measure is strictly monotone.
* `ProbabilityTheory.cdf_neg`: the reflection formula for a negation-invariant measure.
* `ProbabilityTheory.range_cdf`: the cdf of an atomless open-positive measure has range `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Pointwise

namespace ProbabilityTheory

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}

/-! ### Continuity -/

/-- The cdf is continuous at `x` iff `x` is not an atom. -/
theorem continuousAt_cdf_iff : ContinuousAt (cdf μ) x ↔ μ {x} = 0 := by
  rw [StieltjesFunction.continuousAt_iff_measure_singleton, measure_cdf]

/-- The cdf of a measure without atoms is continuous. -/
theorem continuous_cdf [NullSingletonClass μ] : Continuous (cdf μ) :=
  continuous_iff_continuousAt.2 fun x ↦ (continuousAt_cdf_iff μ).2 (measure_singleton x)

/-! ### Reflection -/

/-- The reflection formula for the cdf of a negation-invariant measure, away from atoms. -/
theorem cdf_neg [μ.IsNegInvariant] (hx : μ {x} = 0) : cdf μ (-x) = 1 - cdf μ x := by
  rw [cdf_eq_real, cdf_eq_real, ← neg_Ici, measureReal_def, μ.measure_neg, ← measureReal_def,
    ← measureReal_congr (Ioi_ae_eq_Ici' hx), ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic]

/-- A negation-invariant measure with no atom at `0` has median `0`. -/
theorem cdf_zero [μ.IsNegInvariant] (h : μ {0} = 0) : cdf μ 0 = 2⁻¹ := by
  linarith [cdf_neg μ h, congrArg (cdf μ) neg_zero]

/-! ### Strict monotonicity -/

section IsOpenPosMeasure

variable [μ.IsOpenPosMeasure]

/-- The cdf of a measure that charges every nonempty open set is strictly monotone. -/
theorem strictMono_cdf : StrictMono (cdf μ) := fun a b hab ↦ by
  have h : 0 < (cdf μ).measure (Ioc a b) := by
    rw [measure_cdf]
    exact (isOpen_Ioo.measure_pos μ (nonempty_Ioo.2 hab)).trans_le
      (measure_mono Ioo_subset_Ioc_self)
  rwa [StieltjesFunction.measure_Ioc, ENNReal.ofReal_pos, sub_pos] at h

theorem cdf_pos (x : ℝ) : 0 < cdf μ x :=
  (cdf_nonneg μ (x - 1)).trans_lt (strictMono_cdf μ (sub_one_lt x))

theorem cdf_lt_one (x : ℝ) : cdf μ x < 1 :=
  (strictMono_cdf μ (lt_add_one x)).trans_le (cdf_le_one μ _)

/-! ### The cdf as an order isomorphism -/

variable [NullSingletonClass μ]

/-- The cdf of an atomless open-positive probability measure as an order isomorphism between `ℝ`
and `(0, 1)`. Its inverse is the quantile function of `μ`. -/
noncomputable def cdfOrderIso : ℝ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective _
    ((strictMono_cdf μ).codRestrict fun x ↦ mem_Ioo.2 ⟨cdf_pos μ x, cdf_lt_one μ x⟩) <|
    ((continuous_cdf μ).subtype_mk _).surjective
      (by rw [tendsto_Ioo_atTop]
          exact tendsto_nhdsWithin_iff.2 ⟨tendsto_cdf_atTop μ, .of_forall (cdf_lt_one μ)⟩)
      (by rw [tendsto_Ioo_atBot]
          exact tendsto_nhdsWithin_iff.2 ⟨tendsto_cdf_atBot μ, .of_forall (cdf_pos μ)⟩)

@[simp]
theorem coe_cdfOrderIso_apply (x : ℝ) : (cdfOrderIso μ x : ℝ) = cdf μ x :=
  rfl

@[simp]
theorem coe_comp_cdfOrderIso : (↑) ∘ cdfOrderIso μ = cdf μ :=
  rfl

theorem range_cdf : range (cdf μ) = Ioo 0 1 := by
  rw [← coe_comp_cdfOrderIso μ, range_comp, (cdfOrderIso μ).range_eq, image_univ, Subtype.range_coe]

end IsOpenPosMeasure

end ProbabilityTheory
