import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Linglib.Core.Analysis.SpecialFunctions.Softmax

/-!
# Softmax: characterization, log-partition function, exponential tilting

Three faces of `Real.softmax` beyond its elementary algebra.

* **Fechnerian characterization** ([adams-messick-1958]): a strictly monotone
  solution of Cauchy's multiplicative equation `g (s + t) = g s * g t` is an
  exponential, so a ratio scale expressed through differences of an interval
  scale is the exponential of that scale — the exponential parameterization is
  forced, not chosen.
* **Log-partition function**: `α ↦ log ∑ᵢ exp (α sᵢ + rᵢ)` is convex, so the
  log-likelihood `α ↦ log (softmax (α • s + r) y)` is concave, with derivative
  the observed minus the expected feature.
* **Exponential tilting**: the partition function, log-sum-exp, and softmax are
  the counting-measure `mgf`, `cgf`, and `Measure.tilted`, and tilting the
  uniform measure by the scores gives the softmax measure — the input to the
  Gibbs variational principle of `Core.Probability.GibbsVariational`.

`[UPSTREAM]`: pure-math characterizations of softmax; no linguistics.

## Main results

* `cauchy_mul_exp`, `luce_fechnerian_exp` — the Fechnerian characterization.
* `convexOn_log_sum_exp`, `hasDerivAt_log_sum_exp`, `concaveOn_log_softmax`,
  `hasDerivAt_log_softmax` — convexity and derivative of the log-partition
  function and of the log-likelihood.
* `ProbabilityTheory.mgf_count`, `ProbabilityTheory.cgf_count`,
  `ProbabilityTheory.hasDerivAt_cgf_count`, `MeasureTheory.tilted_count`,
  `ProbabilityTheory.tilted_uniformOn_univ` — the counting-measure face.
-/

open Real Finset

/-! ### The Fechnerian characterization

A ratio scale `v` and an interval scale `u` for one ordering are related by
`v x / v y = g (u x - u y)` for a strictly monotone `g`; transitivity of ratios
forces Cauchy's multiplicative equation, whose strictly monotone solutions are
exponentials ([adams-messick-1958]). -/

/-- A strictly monotone solution of Cauchy's multiplicative functional equation
`g (s + t) = g s * g t` is an exponential `exp (k * s)` with `k > 0`. -/
theorem cauchy_mul_exp (g : ℝ → ℝ) (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) : ∃ k : ℝ, 0 < k ∧ g 0 = 1 ∧ ∀ s, g s = exp (k * s) := by
  have h1 := hg_mono (show (-1 : ℝ) < 0 by norm_num)
  have h2 := hg_mono (show (0 : ℝ) < 1 by norm_num)
  have hne : g 0 ≠ 0 := fun h => by
    have := hg_mul (-1) 1
    rw [neg_add_cancel, h] at this
    rw [h] at h1 h2
    nlinarith
  have h0 : g 0 = 1 := mul_left_cancel₀ hne (by simpa using (hg_mul 0 0).symm)
  have hpos (x : ℝ) : 0 < g x := by
    have hsq : g x = g (x / 2) * g (x / 2) := by rw [← hg_mul, add_halves]
    refine lt_of_le_of_ne (by rw [hsq]; exact mul_self_nonneg _) fun hx => ?_
    have := hg_mul x (-x)
    rw [add_neg_cancel, h0, ← hx, zero_mul] at this
    exact one_ne_zero this
  let h : ℝ →+ ℝ :=
    { toFun := fun x => log (g x)
      map_zero' := by simp [h0]
      map_add' := fun s t => by simp only [hg_mul, log_mul (hpos s).ne' (hpos t).ne'] }
  have hmono : StrictMono h := fun a b hab => log_lt_log (hpos a) (hg_mono hab)
  have hcont : Continuous h :=
    h.continuous_of_isBounded_nhds_zero (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)
      ((Metric.isBounded_Icc (h (-1)) (h 1)).subset hmono.monotone.image_Icc_subset)
  refine ⟨h 1, by simpa using hmono one_pos, h0, fun s => ?_⟩
  have hs : h s = s * h 1 := by simpa using map_real_smul h hcont s 1
  rw [← exp_log (hpos s), mul_comm]
  exact congrArg exp hs

/-- **Fechnerian uniqueness** ([adams-messick-1958]): if a ratio scale `v` and an
interval scale `u` represent the same ordering via `v x / v y = g (u x - u y)` for
a strictly monotone multiplicative `g`, then `v` is the exponential of `u`. -/
theorem luce_fechnerian_exp {X : Type*} (v u : X → ℝ) (g : ℝ → ℝ)
    (hv_pos : ∀ x, 0 < v x)
    (h_ratio : ∀ x y, v x / v y = g (u x - u y))
    (hg_mul : ∀ s t, g (s + t) = g s * g t)
    (hg_mono : StrictMono g) :
    ∃ k : ℝ, 0 < k ∧ ∀ x₀ x, v x = v x₀ * exp (k * (u x - u x₀)) := by
  obtain ⟨k, hk, _, hg_exp⟩ := cauchy_mul_exp g hg_mul hg_mono
  exact ⟨k, hk, fun x₀ x => by
    have h := h_ratio x x₀
    rw [hg_exp (u x - u x₀)] at h
    rwa [div_eq_iff (ne_of_gt (hv_pos x₀)), mul_comm] at h⟩

/-! ### The log-partition function -/

section LogPartition

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The log-partition function is convex in the weight. -/
theorem convexOn_log_sum_exp (s r : ι → ℝ) :
    ConvexOn ℝ Set.univ fun α : ℝ => log (∑ i, exp (α * s i + r i)) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp [show b = 1 from by linarith]
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp [show a = 1 from by linarith]
    have hexp_split (i : ι) : exp ((a * x + b * y) * s i + r i) =
        (exp (x * s i + r i)) ^ a * (exp (y * s i + r i)) ^ b := by
      rw [← exp_mul, ← exp_mul, ← exp_add]
      congr 1
      linear_combination -(r i) * hab
    have hpq : a⁻¹.HolderConjugate b⁻¹ := HolderConjugate.inv_inv ha_pos hb_pos hab
    have holder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ (α := ι)) hpq
      (f := fun i => (exp (x * s i + r i)) ^ a)
      (g := fun i => (exp (y * s i + r i)) ^ b)
      (fun i _ => rpow_nonneg (exp_pos _).le a) (fun i _ => rpow_nonneg (exp_pos _).le b)
    conv at holder => lhs; arg 2; ext i; rw [← hexp_split]
    have hsimp_f (i : ι) : ((exp (x * s i + r i)) ^ a) ^ a⁻¹ = exp (x * s i + r i) := by
      rw [← rpow_mul (exp_pos _).le, mul_inv_cancel₀ ha_pos.ne', rpow_one]
    have hsimp_g (i : ι) : ((exp (y * s i + r i)) ^ b) ^ b⁻¹ = exp (y * s i + r i) := by
      rw [← rpow_mul (exp_pos _).le, mul_inv_cancel₀ hb_pos.ne', rpow_one]
    simp_rw [hsimp_f, hsimp_g] at holder
    simp only [one_div, inv_inv] at holder
    have hZ_x : (0 : ℝ) < ∑ i : ι, exp (x * s i + r i) := sum_exp_pos _
    have hZ_y : (0 : ℝ) < ∑ i : ι, exp (y * s i + r i) := sum_exp_pos _
    have hZ_mid : (0 : ℝ) < ∑ j : ι, exp ((a * x + b * y) * s j + r j) := sum_exp_pos _
    have hlog_le := log_le_log hZ_mid holder
    rw [log_mul (rpow_pos_of_pos hZ_x a).ne' (rpow_pos_of_pos hZ_y b).ne', log_rpow hZ_x,
      log_rpow hZ_y] at hlog_le
    linarith

/-- The derivative of the log-partition function is the expected feature value. -/
theorem hasDerivAt_log_sum_exp (s r : ι → ℝ) (α : ℝ) :
    HasDerivAt (fun α => log (∑ i, exp (α * s i + r i)))
      (∑ i, softmax (α • s + r) i * s i) α := by
  simp only [softmax_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hexp (j : ι) : HasDerivAt (fun a => exp (a * s j + r j)) (exp (α * s j + r j) * s j) α :=
    (hasDerivAt_exp _).comp α (by simpa using ((hasDerivAt_id α).mul_const (s j)).add_const (r j))
  have hsum : HasDerivAt (fun a => ∑ j : ι, exp (a * s j + r j))
      (∑ j : ι, exp (α * s j + r j) * s j) α :=
    HasDerivAt.fun_sum fun j _ => hexp j
  convert hsum.log (sum_exp_pos _).ne' using 1
  rw [sum_div]
  exact sum_congr rfl fun i _ => by ring

/-- The log-likelihood `α ↦ log (softmax (α • s + r) y)` is concave: affine minus
convex. -/
theorem concaveOn_log_softmax (s r : ι → ℝ) (y : ι) :
    ConcaveOn ℝ Set.univ fun α : ℝ => log (softmax (α • s + r) y) := by
  simp only [log_softmax, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ConcaveOn.sub ⟨convex_univ, fun x _ z _ a b ha hb hab => ?_⟩ (convexOn_log_sum_exp s r)
  simp only [smul_eq_mul]
  nlinarith [show a * r y + b * r y = r y from by linear_combination (r y) * hab]

/-- The derivative of the log-likelihood is the observed minus the expected
feature value. -/
theorem hasDerivAt_log_softmax (s r : ι → ℝ) (y : ι) (α : ℝ) :
    HasDerivAt (fun α => log (softmax (α • s + r) y))
      (s y - ∑ i, softmax (α • s + r) i * s i) α := by
  simp only [log_softmax, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h_affine : HasDerivAt (fun a => a * s y + r y) (s y) α := by
    simpa using ((hasDerivAt_id α).mul_const (s y)).add_const (r y)
  exact h_affine.sub (hasDerivAt_log_sum_exp s r α)

end LogPartition

/-! ### Exponential tilting and the cumulant generating function

Softmax is the finite, counting-measure case of mathlib's exponential-family
machinery: the partition function `∑ i, exp (α * s i)` is the moment generating
function of the scores, log-sum-exp is the cumulant generating function, and
softmax is the density of the exponentially tilted counting measure. -/

section Tilting

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

@[simp] theorem ProbabilityTheory.mgf_count (s : ι → ℝ) (α : ℝ) :
    mgf s Measure.count α = ∑ i, exp (α * s i) := by
  simp [mgf]

@[simp] theorem ProbabilityTheory.cgf_count (s : ι → ℝ) (α : ℝ) :
    cgf s Measure.count α = log (∑ i, exp (α * s i)) := by
  simp [cgf]

/-- The derivative of the cumulant generating function is the expected score under
the softmax. -/
theorem ProbabilityTheory.hasDerivAt_cgf_count [Nonempty ι] (s : ι → ℝ) (α : ℝ) :
    HasDerivAt (cgf s Measure.count) (∑ i, softmax (α • s) i * s i) α := by
  simpa [funext (cgf_count s)] using hasDerivAt_log_sum_exp s 0 α

/-- Softmax is the density of the exponentially tilted counting measure. -/
theorem MeasureTheory.tilted_count (s : ι → ℝ) :
    Measure.count.tilted s = Measure.count.withDensity fun i => ENNReal.ofReal (softmax s i) := by
  simp [Measure.tilted, softmax_def]

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The uniform measure is the counting measure tilted by zero. -/
theorem ProbabilityTheory.uniformOn_univ_eq_tilted_zero :
    uniformOn (Set.univ : Set ι) = Measure.count.tilted 0 := by
  rw [tilted_zero', uniformOn, cond, Measure.restrict_univ]

/-- Tilting the uniform measure by the scores gives the softmax measure. -/
theorem ProbabilityTheory.tilted_uniformOn_univ (s : ι → ℝ) :
    (uniformOn (Set.univ : Set ι)).tilted s = Measure.count.tilted s := by
  rw [uniformOn_univ_eq_tilted_zero, tilted_tilted (Integrable.of_finite), zero_add]

end Tilting
