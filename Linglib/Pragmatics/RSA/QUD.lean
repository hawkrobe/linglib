module

public import Linglib.Pragmatics.RSA.Basic

/-!
# QUD-projected listeners

A communicative goal projects the meaning space onto the topic under discussion, and a speaker
with that goal is informative about the listener's mass on the cell of the intended meaning
rather than on the meaning itself. Kao and colleagues use this projected literal listener for
metaphor, hyperbole and irony. `RSA.projListener` is that listener as a kernel, so that with
the goal as a state-side latent the goal-indexed speaker is `RSA.familySpeaker` of the projected
listeners and the listener who marginalizes the goal is `RSA.familyListener`.

A literally false utterance projects positive mass onto a meaning exactly when the meaning's
cell contains a literally true one (`RSA.projListener_apply_singleton_ne_zero_iff`), the
mechanism of nonliteral interpretation; a goal that projects injectively leaves the literal
listener unchanged (`RSA.projListener_apply_singleton_of_injective`).

## References

* [kao-etal-2014-metaphor], [kao-etal-2014-hyperbole], [kao-goodman-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section ProjListener

variable {W U G X : Type*} [MeasurableSpace W] [MeasurableSpace U] [Countable U]
  [MeasurableSingletonClass U] [Fintype W] [MeasurableSingletonClass W]

/-- The QUD-projected listener puts at each meaning the listener's mass on the meaning's cell
under the goal's projection. It is not normalized, since the speaker's best response reads only
its weights. -/
noncomputable def projListener (project : G → W → X) (L : Kernel U W) (g : G) : Kernel U W :=
  Kernel.ofFunOfCountable λ u => ∑ w, L u (project g ⁻¹' {project g w}) • Measure.dirac w

variable (project : G → W → X) (L : Kernel U W) (g : G) (u : U) (w : W)

@[simp] theorem projListener_apply_singleton :
    projListener project L g u {w} = L u (project g ⁻¹' {project g w}) := by
  rw [projListener, Kernel.ofFunOfCountable_apply]
  exact Measure.sum_smul_dirac_apply_singleton (λ w' => L u (project g ⁻¹' {project g w'})) w

/-- The projected listener of a finite kernel is finite, since each row puts at most the
listener's bound on each of the finitely many meanings. -/
instance [IsFiniteKernel L] : IsFiniteKernel (projListener project L g) :=
  ⟨⟨Fintype.card W * L.bound,
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) L.bound_lt_top, fun u ↦ by
      rw [← Finset.coe_univ, ← sum_measure_singleton, ← nsmul_eq_mul, ← Finset.card_univ]
      exact Finset.sum_le_card_nsmul _ _ _ fun w _ ↦ by
        rw [projListener_apply_singleton]; exact L.measure_le_bound u _⟩⟩

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

/-- Within a context set, the projected literal listener of a Boolean meaning on a weight prior
is the weight of the context-set worlds that make the utterance true and share the meaning's
cell, over the weight of those that make it true. -/
theorem projListener_literalListener_restrict_apply_singleton [DiscreteMeasurableSpace W]
    [DecidableEq X] (P : W → ℕ) (C : Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] :
    projListener project
        (literalListener ((priorOfWeights P).restrict ↑C) sem) g u {w}
      = (∑ v ∈ (C.filter (· ∈ sem u)).filter (λ v => project g v = project g w), (P v : ℝ≥0∞))
          / ∑ v ∈ C.filter (· ∈ sem u), (P v : ℝ≥0∞) := by
  have e1 : sem u ∩ ↑C = ↑(C.filter (· ∈ sem u)) := by ext; simp [and_comm]
  have e2 : sem u ∩ project g ⁻¹' {project g w} ∩ ↑C
      = ↑((C.filter (· ∈ sem u)).filter λ v => project g v = project g w) := by
    ext; simp; tauto
  rw [projListener_apply_singleton, literalListener_apply, cond_apply .of_discrete,
    Measure.restrict_apply .of_discrete, Measure.restrict_apply .of_discrete, e1, e2,
    priorOfWeights_apply_finset, priorOfWeights_apply_finset, ENNReal.div_eq_inv_mul]

end ProjListener

end RSA
