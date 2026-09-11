import Linglib.Pragmatics.RSA.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# QUD-projected listeners

A communicative goal projects the meaning space onto the topic under discussion, and a speaker
with that goal is informative about the listener's mass on the cell of the intended meaning
rather than on the meaning itself: the projected literal listener of [kao-etal-2014-metaphor]
(eq. 1), [kao-etal-2014-hyperbole] (eq. 6) and [kao-goodman-2015]. `RSA.projListener` is that
listener as a kernel, so that with the goal as a state-side latent the goal-indexed speaker is
`RSA.familySpeaker` of the projected listeners and the listener who marginalizes the goal is
`RSA.familyListener` ([kao-etal-2014-hyperbole] eq. 10).

A literally false utterance projects positive mass onto a meaning exactly when the meaning's
cell contains a literally true one (`RSA.projListener_apply_singleton_ne_zero_iff`), the
mechanism of nonliteral interpretation; a goal that projects injectively leaves the literal
listener unchanged (`RSA.projListener_apply_singleton_of_injective`).

## References

* [kao-etal-2014-metaphor], [kao-etal-2014-hyperbole], [kao-goodman-2015]
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section ProjListener

variable {W U G X : Type*} [MeasurableSpace W] [MeasurableSpace U] [Countable U]
  [MeasurableSingletonClass U] [Fintype W] [MeasurableSingletonClass W]

/-- The QUD-projected listener: at each meaning, the listener's mass on the meaning's cell under
the goal's projection. It is not normalized; the speaker's best response reads only its
weights. -/
noncomputable def projListener (project : G → W → X) (L : Kernel U W) (g : G) : Kernel U W :=
  Kernel.ofFunOfCountable λ u => ∑ w, L u (project g ⁻¹' {project g w}) • Measure.dirac w

variable (project : G → W → X) (L : Kernel U W) (g : G) (u : U) (w : W)

@[simp] theorem projListener_apply_singleton :
    projListener project L g u {w} = L u (project g ⁻¹' {project g w}) := by
  rw [projListener, Kernel.ofFunOfCountable_apply]
  exact Measure.sum_smul_dirac_apply_singleton (λ w' => L u (project g ⁻¹' {project g w'})) w

/-- The cell's mass is the sum of the listener's masses over the cell. -/
theorem projListener_apply_singleton_eq_sum [DecidableEq X] :
    projListener project L g u {w}
      = ∑ w' ∈ Finset.univ.filter (λ w' => project g w' = project g w), L u {w'} := by
  rw [projListener_apply_singleton, sum_measure_singleton]
  congr 1
  ext w'
  simp

/-- The meaning lies in its own cell. -/
theorem apply_singleton_le_projListener : L u {w} ≤ projListener project L g u {w} := by
  rw [projListener_apply_singleton]
  exact measure_mono (Set.singleton_subset_iff.mpr rfl)

/-- The projected listener is a subprobability wherever the listener is. -/
theorem projListener_apply_singleton_le_one (h : ∀ u s, L u s ≤ 1) :
    projListener project L g u {w} ≤ 1 := by
  rw [projListener_apply_singleton]
  exact h u _

/-- A meaning receives positive projected mass exactly when its cell contains a meaning of
positive literal mass. -/
theorem projListener_apply_singleton_ne_zero_iff [DecidableEq X] :
    projListener project L g u {w} ≠ 0 ↔ ∃ w', project g w' = project g w ∧ L u {w'} ≠ 0 := by
  rw [projListener_apply_singleton_eq_sum, ne_eq, Finset.sum_eq_zero_iff]
  simp

/-- A goal that projects injectively leaves the literal listener unchanged. -/
theorem projListener_apply_singleton_of_injective (h : Function.Injective (project g)) :
    projListener project L g u {w} = L u {w} := by
  rw [projListener_apply_singleton, ← Set.image_singleton, h.preimage_image]

end ProjListener

end RSA

/-! ### QUD-projected aggregation of weights

The finite-sum form of the projection over weight functions, consumed by the studies not yet
on the kernel pipeline. -/

namespace RSA.QUD

/-- QUD-projected aggregation: sum of `weight w'` over the
QUD-equivalence class of `w` under projection `project g`. -/
noncomputable def proj {W G β : Type*} [Fintype W] [DecidableEq β]
    (project : G → W → β) (weight : W → ℝ≥0∞) (g : G) (w : W) : ℝ≥0∞ :=
  ∑ w' ∈ (Finset.univ : Finset W).filter (fun w' => project g w' = project g w),
    weight w'

variable {W G β : Type*} [Fintype W] [DecidableEq β]
  (project : G → W → β) (weight : W → ℝ≥0∞) (g : G) (w : W)

/-- The world `w` is in its own QUD-equivalence class, so its weight
provides a lower bound on the QUD-projected aggregation. -/
theorem self_le_proj : weight w ≤ proj project weight g w :=
  Finset.single_le_sum (f := weight) (fun _ _ => zero_le)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- The QUD-projected aggregation is positive iff some world in the same QUD-equivalence class
has positive weight. -/
theorem proj_pos_iff_exists_class_member :
    0 < proj project weight g w ↔
      ∃ w' ∈ (Finset.univ : Finset W).filter
              (fun w' => project g w' = project g w),
        0 < weight w' :=
  Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le)

/-- The QUD-projected aggregation is bounded by the total weight. -/
theorem proj_le_total : proj project weight g w ≤ ∑ w' : W, weight w' :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end RSA.QUD

namespace RSA.QUD

variable {W G β : Type*} [Fintype W] [DecidableEq β]
  (project : G → W → β) (p : PMF W) (g : G) (w : W)

/-- When the weight is a PMF, the QUD-projected aggregation is bounded
by 1 (the equivalence class is a subset of the support). -/
theorem proj_le_one_of_pmf : proj project (⇑p) g w ≤ 1 := by
  calc proj project (⇑p) g w
      ≤ ∑ w' : W, p w' := proj_le_total project (⇑p) g w
    _ = ∑' w' : W, p w' := (tsum_fintype _).symm
    _ = 1 := p.tsum_coe

/-- When the weight is a PMF, the QUD-projected aggregation is finite. -/
theorem proj_ne_top_of_pmf : proj project (⇑p) g w ≠ ⊤ :=
  (lt_of_le_of_lt (proj_le_one_of_pmf project p g w) ENNReal.one_lt_top).ne

end RSA.QUD
