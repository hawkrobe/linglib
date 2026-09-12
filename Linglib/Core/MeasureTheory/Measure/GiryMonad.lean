/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Monotonicity and ω-continuity of the Giry monad

`Measure.bind` is monotone in both arguments and commutes with suprema of monotone sequences in
both arguments. Together with the complete lattice structure on `Measure α`, this makes an
operator built from `bind` ω-Scott-continuous, so its least fixed point is the supremum of its
Kleene iterates (`OrderHom.lfp_eq_sSup_iterate`). This is the least-fixed-point semantics of
recursive probabilistic programs of [kozen-1981], stated on the monad of [giry-1982].
`[UPSTREAM]` candidate for `Mathlib/MeasureTheory/Measure/GiryMonad.lean`.

## Main results

* `MeasureTheory.Measure.bind_mono`: `bind` is monotone in the measure and in the kernel.
* `MeasureTheory.Measure.iSup_apply_of_monotone`: the supremum of a monotone sequence of measures
  is computed pointwise on measurable sets.
* `MeasureTheory.lintegral_iSup_measure_of_monotone`: Lebesgue integrals commute with monotone
  suprema of measures.
* `MeasureTheory.Measure.iSup_bind_of_monotone`, `MeasureTheory.Measure.bind_iSup_of_monotone`:
  `bind` commutes with monotone suprema in each argument.

## References

* [giry-1982]
* [kozen-1981]
-/

open MeasureTheory
open scoped ENNReal

namespace ENNReal

/-- A supremum over a monotone sequence commutes with a countable sum. -/
theorem iSup_tsum_of_monotone {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {g : ℕ → ι → ℝ≥0∞} (hg : Monotone g) :
    ⨆ n, ∑' i, g n i = ∑' i, ⨆ n, g n i := by
  simp_rw [← lintegral_count]
  exact (lintegral_iSup (fun n => measurable_of_countable (g n)) hg).symm

end ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Measure

theorem bind_mono_left {μ ν : Measure α} {f : α → Measure β} (hμν : μ ≤ ν)
    (hf : AEMeasurable f ν) : μ.bind f ≤ ν.bind f := by
  refine le_iff.2 fun s hs => ?_
  rw [bind_apply hs (hf.mono_measure hμν), bind_apply hs hf]
  exact lintegral_mono' hμν le_rfl

theorem bind_mono_right {μ : Measure α} {f g : α → Measure β} (hfg : ∀ a, f a ≤ g a)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : μ.bind f ≤ μ.bind g := by
  refine le_iff.2 fun s hs => ?_
  rw [bind_apply hs hf, bind_apply hs hg]
  exact lintegral_mono fun a => le_iff'.1 (hfg a) s

theorem bind_mono {μ ν : Measure α} {f g : α → Measure β} (hμν : μ ≤ ν)
    (hfg : ∀ a, f a ≤ g a)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) : μ.bind f ≤ ν.bind g :=
  (bind_mono_right hfg hf (hg.mono_measure hμν)).trans (bind_mono_left hμν hg)

/-- The supremum of a monotone sequence of measures is computed pointwise on measurable sets. -/
theorem iSup_apply_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) {s : Set α}
    (hs : MeasurableSet s) : (⨆ n, μ n) s = ⨆ n, μ n s := by
  let ν : Measure α := ofMeasurable (fun s _ => ⨆ n, μ n s) (by simp) fun f hf hd => by
    simp_rw [measure_iUnion hd hf]
    exact ENNReal.iSup_tsum_of_monotone fun m n h i => le_iff.1 (hμ h) _ (hf i)
  have hν : (⨆ n, μ n) = ν := by
    refine le_antisymm (iSup_le fun n => le_iff.2 fun s hs => ?_) (le_iff.2 fun s hs => ?_)
    · rw [ofMeasurable_apply s hs]
      exact le_iSup (fun n => μ n s) n
    · rw [ofMeasurable_apply s hs]
      exact iSup_le fun n => le_iff.1 (le_iSup μ n) s hs
  rw [hν, ofMeasurable_apply s hs]

end Measure

/-- Simple-function integrals commute with monotone suprema of measures. -/
theorem SimpleFunc.lintegral_iSup_measure_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ)
    (g : SimpleFunc α ℝ≥0∞) : g.lintegral (⨆ n, μ n) = ⨆ n, g.lintegral (μ n) := by
  simp only [SimpleFunc.lintegral]
  simp_rw [Measure.iSup_apply_of_monotone hμ (g.measurableSet_preimage _), ENNReal.mul_iSup]
  refine ENNReal.finsetSum_iSup fun i j => ⟨max i j, fun x => ⟨?_, ?_⟩⟩ <;> gcongr
  exacts [hμ (le_max_left i j), hμ (le_max_right i j)]

/-- Lebesgue integrals commute with monotone suprema of measures. -/
theorem lintegral_iSup_measure_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ)
    (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂μ n := by
  simp_rw [lintegral_def, SimpleFunc.lintegral_iSup_measure_of_monotone hμ]
  rw [iSup_comm]
  exact iSup_congr fun g => iSup_comm

namespace Measure

theorem iSup_bind_of_monotone {μ : ℕ → Measure α} (hμ : Monotone μ) {f : α → Measure β}
    (hf : Measurable f) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  ext s hs
  rw [bind_apply hs hf.aemeasurable,
    iSup_apply_of_monotone (fun m n h => bind_mono_left (hμ h) hf.aemeasurable) hs,
    lintegral_iSup_measure_of_monotone hμ]
  simp_rw [bind_apply hs hf.aemeasurable]

theorem bind_iSup_of_monotone {μ : Measure α} {f : ℕ → α → Measure β}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) : μ.bind (fun a => ⨆ n, f n a) = ⨆ n, μ.bind (f n) := by
  have hpt : ∀ a, ∀ {s : Set β}, MeasurableSet s → (⨆ n, f n a) s = ⨆ n, f n a s :=
    fun a _ hs => iSup_apply_of_monotone (fun m n h => hmono h a) hs
  have hmeas : Measurable fun a => ⨆ n, f n a :=
    measurable_of_measurable_coe _ fun s hs => by
      simp_rw [hpt _ hs]
      exact Measurable.iSup fun n => (measurable_coe hs).comp (hf n)
  ext s hs
  rw [bind_apply hs hmeas.aemeasurable,
    iSup_apply_of_monotone
      (fun m n h =>
        bind_mono_right (fun a => hmono h a) (hf m).aemeasurable (hf n).aemeasurable) hs]
  simp_rw [bind_apply hs (hf _).aemeasurable, hpt _ hs]
  exact lintegral_iSup (fun n => (measurable_coe hs).comp (hf n))
    fun m n h a => le_iff'.1 (hmono h a) s

end Measure

end MeasureTheory
