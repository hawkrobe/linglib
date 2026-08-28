import Linglib.Discourse.CommonGround
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# The common ground of a measure

This file makes a measure over worlds a discourse state: its common ground is its
almost-everywhere filter — what holds almost surely is mutually accepted — and its context
set is the set of positive-mass worlds. A graded common ground of this kind is
[anderson-2021]'s, updated by mixture rather than by intersection.

## Main results

* `HasCommonGround.contextSet_measure`: the context set of `μ` is `{w | μ {w} ≠ 0}`.

## References

* [stalnaker-2002] — the context set
* [anderson-2021] — the common ground as a distribution over worlds
-/

open MeasureTheory

variable {W : Type*} [MeasurableSpace W]

instance : HasCommonGround (Measure W) W := ⟨ae⟩

@[simp] theorem HasCommonGround.commonGround_measure (μ : Measure W) : commonGround μ = ae μ :=
  rfl

theorem HasCommonGround.contextSet_measure (μ : Measure W) : contextSet μ = {w | μ {w} ≠ 0} := by
  ext w
  simp only [contextSet, commonGround_measure, Filter.mem_ker, mem_ae_iff, Set.mem_ofPred_eq]
  exact ⟨fun h h0 => h {w}ᶜ (by rwa [compl_compl]) rfl, fun h s hs => by_contra fun hw =>
    h (measure_mono_null (Set.singleton_subset_iff.mpr hw) hs)⟩
