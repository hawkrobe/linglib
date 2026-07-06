import Linglib.Processing.Lexical.Discriminative.Training
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Existence of ERM solutions
[gahl-baayen-2024] [heitmeier-2024]

ERM solutions exist for any nonnegative frequency vector: each observed form
column is orthogonally projected onto the prediction subspace
(`Submodule.starProjection`), and the columns assemble through
`isERMSolution_iff_coordResidual`. The normal-equations solvability of
[gahl-baayen-2024]'s appendix, with no invertibility hypothesis.
-/

namespace Processing.Lexical.Discriminative

noncomputable section

variable {m n d : ℕ}

private theorem coordResidual_uniform_eq_norm_sq (data : TrainingExperience m n d)
    (pred : Fin m → ℝ) (j : Fin n) :
    coordResidual data (uniformFrequency m) pred j
      = ‖WithLp.toLp 2 (fun k => data.forms k j)
          - WithLp.toLp 2 pred‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold coordResidual
  refine Finset.sum_congr rfl fun k _ => ?_
  show 1 * (pred k - data.forms k j) ^ 2 = _
  rw [one_mul, ← WithLp.toLp_sub]
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  ring

private theorem exists_forall_coordResidual_le (data : TrainingExperience m n d)
    (j : Fin n) :
    ∃ w : MeaningVec d →ₗ[ℝ] ℝ, ∀ w' : MeaningVec d →ₗ[ℝ] ℝ,
      coordResidual data (uniformFrequency m) (fun k => w (data.meanings k)) j
        ≤ coordResidual data (uniformFrequency m) (fun k => w' (data.meanings k)) j := by
  classical
  -- prediction subspace: range of the evaluation map into Euclidean event space
  set Ev : (MeaningVec d →ₗ[ℝ] ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi fun k => LinearMap.applyₗ (data.meanings k)) with hEv
  set y : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun k => data.forms k j) with hy
  haveI : CompleteSpace ↥(LinearMap.range Ev) := FiniteDimensional.complete ℝ _
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ((LinearMap.range Ev).starProjection_apply_mem y)
  refine ⟨w, fun w' => ?_⟩
  have hmin : ∀ v : ↥(LinearMap.range Ev),
      ‖y - (LinearMap.range Ev).starProjection y‖ ≤ ‖y - ↑v‖ := fun v => by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro r ⟨x, rfl⟩; exact norm_nonneg _⟩ v
  have hle : ‖y - Ev w‖ ≤ ‖y - Ev w'‖ := by
    rw [hw]
    exact hmin ⟨Ev w', LinearMap.mem_range_self _ _⟩
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hEvw : ∀ v : MeaningVec d →ₗ[ℝ] ℝ,
      Ev v = WithLp.toLp 2 (fun k => v (data.meanings k)) := fun _ => rfl
  rw [coordResidual_uniform_eq_norm_sq, coordResidual_uniform_eq_norm_sq]
  rw [hEvw w, hEvw w', hy] at hsq
  exact hsq

/-- Endstate solutions exist — the normal-equations
    solvability of [gahl-baayen-2024]'s appendix, by orthogonal projection
    of each observed form column onto the prediction subspace. -/
theorem exists_isELSolution (data : TrainingExperience m n d) :
    ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, IsELSolution data G := by
  choose w hw using exists_forall_coordResidual_le data
  refine ⟨LinearMap.pi w, (isERMSolution_iff_coordResidual _ _ _).mpr fun j w' => ?_⟩
  simpa only [LinearMap.pi_apply] using hw j w'

/-- ERM solutions exist for any nonnegative frequency
    vector, via `exists_isELSolution` on the `√q`-premultiplied experience. -/
theorem exists_isERMSolution (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i) :
    ∃ G, IsERMSolution data q G :=
  let ⟨G, hG⟩ := exists_isELSolution (data.sqrtScale q)
  ⟨G, (isELSolution_sqrtScale_iff hq).mp hG⟩


end

end Processing.Lexical.Discriminative
