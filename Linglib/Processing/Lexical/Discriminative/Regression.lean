import Linglib.Core.Analysis.LeastSquares
import Linglib.Processing.Lexical.Discriminative.Training
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# DLM training as weighted regression
[gahl-baayen-2024] [heitmeier-2024]

The weighted loss is a least-squares residual: `√q`-scaling embeds the
training objective into `EuclideanSpace ℝ (Fin m × Fin n)`
(`weightedLoss_eq_norm_sq`), identifying the ERM solutions with the
least-squares solutions of the design map (`isERMSolution_iff_isLeastSquares`).
Existence then follows from the Hilbert projection theorem via
`Core.exists_isLeastSquares` — the normal-equations solvability of
[gahl-baayen-2024]'s appendix, with no invertibility hypothesis.
-/

namespace Processing.Lexical.Discriminative

noncomputable section

variable {m n d : ℕ}

/-- The `√q`-scaled **design map**: the linear embedding of candidate
    production maps into Euclidean event-coordinate space whose residual
    against `scaledTarget` is the weighted loss. -/
def designMap (data : TrainingExperience m n d) (q : FrequencyVector m) :
    (MeaningVec d →ₗ[ℝ] FormVec n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun p => Real.sqrt (q p.1) •
      (LinearMap.proj p.2 ∘ₗ LinearMap.applyₗ (data.meanings p.1))

@[simp] theorem designMap_apply (data : TrainingExperience m n d)
    (q : FrequencyVector m) (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (p : Fin m × Fin n) :
    designMap data q G p = Real.sqrt (q p.1) * G (data.meanings p.1) p.2 := rfl

/-- The `√q`-scaled observed forms, as a point of Euclidean
    event-coordinate space. -/
def scaledTarget (data : TrainingExperience m n d) (q : FrequencyVector m) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 fun p => Real.sqrt (q p.1) * data.forms p.1 p.2

/-- The weighted loss is the squared least-squares residual of the design
    map against the scaled target. -/
theorem weightedLoss_eq_norm_sq (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    (G : MeaningVec d →ₗ[ℝ] FormVec n) :
    weightedLoss data q G
      = ‖designMap data q G - scaledTarget data q‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold weightedLoss squaredDist
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : (Real.sqrt (q i) * G (data.meanings i) j
        - Real.sqrt (q i) * data.forms i j) ^ 2
      = Real.sqrt (q i) ^ 2 * (G (data.meanings i) j - data.forms i j) ^ 2 := by
    ring
  simp only [PiLp.sub_apply, designMap_apply, scaledTarget,
             Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sq_sqrt (hq i)]

/-- ERM solutions are exactly the least-squares solutions of the design
    map — the DLM training problem, seen through `√q`-scaling, is weighted
    linear regression. -/
theorem isERMSolution_iff_isLeastSquares (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} :
    IsERMSolution data q G
      ↔ Core.IsLeastSquares (designMap data q) (scaledTarget data q) G := by
  unfold IsERMSolution Core.IsLeastSquares
  refine forall_congr' fun G' => ?_
  rw [weightedLoss_eq_norm_sq data hq, weightedLoss_eq_norm_sq data hq]
  constructor
  · intro h
    have hroot := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot
  · intro h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- ERM solutions exist for any nonnegative frequency vector, by the
    Hilbert projection theorem (`Core.exists_isLeastSquares`). -/
theorem exists_isERMSolution (data : TrainingExperience m n d)
    {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i) :
    ∃ G, IsERMSolution data q G := by
  haveI : CompleteSpace ↥(LinearMap.range (designMap data q)) :=
    FiniteDimensional.complete ℝ _
  obtain ⟨G, hG⟩ := Core.exists_isLeastSquares
    (A := designMap data q) (b := scaledTarget data q)
  exact ⟨G, (isERMSolution_iff_isLeastSquares data hq).mpr hG⟩

/-- Endstate solutions exist. -/
theorem exists_isELSolution (data : TrainingExperience m n d) :
    ∃ G : MeaningVec d →ₗ[ℝ] FormVec n, IsELSolution data G :=
  exists_isERMSolution data fun _ => zero_le_one

end

end Processing.Lexical.Discriminative
