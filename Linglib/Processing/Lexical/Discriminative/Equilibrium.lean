import Linglib.Core.Learning.WidrowHoff
import Linglib.Processing.Lexical.Discriminative.Training

/-!
# The endstate of learning as Widrow-Hoff equilibrium
[heitmeier-2024] [gahl-baayen-2024] [widrow-hoff-1960]

`isERMSolution_iff_whEquilibrium`: `G` is an ERM solution iff the
frequency-weighted total Widrow-Hoff correction (`Core.whCorrection`)
vanishes — the fixed-point half of the sources' convergence-defined
*endstate* ([gahl-baayen-2024] appendix; trajectory convergence is TODO).
The equilibrium is order-invariant by construction, whereas the incremental
trajectory is order- and rate-dependent ([heitmeier-2024]).
-/

namespace Processing.Lexical.Discriminative

open Core

noncomputable section

variable {m n d : ℕ}

private theorem sum_mul_comm (x y : Fin d → ℝ) :
    ∑ l, x l * y l = Fintype.linearCombination ℝ x y := by
  rw [Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, mul_comm]

/-- Every linear functional on `MeaningVec d` is a linear combination of its
    basis values. -/
private theorem eq_linearCombination (w : MeaningVec d →ₗ[ℝ] ℝ) :
    w = Fintype.linearCombination ℝ
      (fun l => w fun j' => if l = j' then 1 else 0) := by
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.pi_apply_eq_sum_univ w s, Fintype.linearCombination_apply]

private theorem sum_whCorrection_apply (data : TrainingExperience m n d)
    (q : FrequencyVector m) (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (s' : MeaningVec d) (j : Fin n) :
    (∑ i, q i • whCorrection (data.meanings i) (data.forms i) G) s' j
      = ∑ i, q i * ((data.forms i j - G (data.meanings i) j)
          * Fintype.linearCombination ℝ s' (data.meanings i)) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, whCorrection_apply,
             Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_mul_comm s' (data.meanings i)]
  ring

/-- The error-form and residual-form pairings sum to zero. -/
private theorem errorSum_add_residSum (data : TrainingExperience m n d)
    (q : FrequencyVector m) (G : MeaningVec d →ₗ[ℝ] FormVec n)
    (s' : MeaningVec d) (j : Fin n) :
    (∑ i, q i * ((data.forms i j - G (data.meanings i) j)
        * Fintype.linearCombination ℝ s' (data.meanings i)))
      + ∑ i, q i * ((G (data.meanings i) j - data.forms i j)
          * Fintype.linearCombination ℝ s' (data.meanings i)) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

/-- `G` is an ERM solution iff the frequency-weighted total Widrow-Hoff
    correction vanishes — the *endstate of learning* is exactly the
    equilibrium (fixed point) of error-driven learning, with no
    invertibility hypothesis. -/
theorem isERMSolution_iff_whEquilibrium
    {data : TrainingExperience m n d} {q : FrequencyVector m} (hq : ∀ i, 0 ≤ q i)
    {G : MeaningVec d →ₗ[ℝ] FormVec n} :
    IsERMSolution data q G ↔
      ∑ i, q i • whCorrection (data.meanings i) (data.forms i) G = 0 := by
  rw [isERMSolution_iff_forall_column hq]
  constructor
  · intro h
    refine LinearMap.ext fun s' => funext fun j => ?_
    rw [sum_whCorrection_apply]
    have hres := h j (Fintype.linearCombination ℝ s')
    have hzero := errorSum_add_residSum data q G s' j
    simp only [LinearMap.zero_apply, Pi.zero_apply]
    linarith
  · intro h j w
    rw [eq_linearCombination w]
    have h0 := congrFun
      (LinearMap.congr_fun h (fun l => w fun j' => if l = j' then 1 else 0)) j
    rw [sum_whCorrection_apply] at h0
    simp only [LinearMap.zero_apply, Pi.zero_apply] at h0
    have hzero := errorSum_add_residSum data q G
      (fun l => w fun j' => if l = j' then 1 else 0) j
    linarith

end

end Processing.Lexical.Discriminative
