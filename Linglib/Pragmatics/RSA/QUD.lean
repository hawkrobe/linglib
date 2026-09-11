import Linglib.Pragmatics.RSA.Basic

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
