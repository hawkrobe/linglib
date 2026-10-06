/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Decision.Blackwell
public import Linglib.Core.Probability.Decision.Basic
public import Linglib.Core.Probability.Decision.ValueOfInformation

/-!
# Question utility and the comparison of experiments

The expected utility value of a partition question is the value of information of the
experiment that reveals the cell of the world (`valueOfInformation_deterministic`). Through this
identification, van Rooy's comparison of questions is Blackwell's comparison of deterministic
experiments: one partition refines another exactly when it is at least as useful in every
decision problem.

## Main statements

* `valueOfInformation_deterministic`: the expected utility value of the question whose cells are
  the fibres of `f` is the value of information of observing `f`.
* `factorsThrough_of_forall_questionUtility_le`: a classifier never more useful than another
  factors through it.
* `le_iff_forall_questionUtility_le`: one partition refines another exactly when it is at least
  as useful in every decision problem with a probability prior.

## References

* [van-rooy-2003]
* [blackwell-1953]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Core.DecisionTheory.DecisionProblem

universe u

variable {W : Type u} {A O O' : Type*} [Fintype W] [DecidableEq W]

/-- The prior of a decision problem as a measure is the weighted sum of Dirac masses
`∑ w, ofReal (prior w) • δ_w`. -/
noncomputable def priorMeasure [MeasurableSpace W] (dp : DecisionProblem ℝ W A) :
    Measure W :=
  ∑ w : W, ENNReal.ofReal (dp.prior w) • Measure.dirac w

@[simp] theorem priorMeasure_singleton [MeasurableSpace W] [MeasurableSingletonClass W]
    (dp : DecisionProblem ℝ W A) (w : W) :
    dp.priorMeasure {w} = ENNReal.ofReal (dp.prior w) := by
  classical
  show (∑ w' : W, ENNReal.ofReal (dp.prior w') • Measure.dirac w') {w}
      = ENNReal.ofReal (dp.prior w)
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ w fun w' ↦ ENNReal.ofReal (dp.prior w')]
  simp

instance [MeasurableSpace W] (dp : DecisionProblem ℝ W A) :
    IsFiniteMeasure dp.priorMeasure := by
  refine ⟨?_⟩
  show (∑ w : W, ENNReal.ofReal (dp.prior w) • Measure.dirac w) Set.univ < ⊤
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun w _ ↦ ?_
  simp [Measure.smul_apply]

omit [DecidableEq W] in
theorem isProbabilityMeasure_priorMeasure [MeasurableSpace W]
    [MeasurableSingletonClass W] (dp : DecisionProblem ℝ W A)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w : W, dp.prior w = 1) :
    IsProbabilityMeasure dp.priorMeasure := by
  refine ⟨?_⟩
  show (∑ w : W, ENNReal.ofReal (dp.prior w) • Measure.dirac w) Set.univ = 1
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun w _ ↦ hprior w, hsum, ENNReal.ofReal_one]

omit [DecidableEq W] in
/-- The fibres of a classifier carry the whole prior mass. -/
private lemma cellProbability_sum_fibers (dp : DecisionProblem ℝ W A)
    {O : Type*} [Fintype O] [DecidableEq O] (classify : W → O)
    (hsum : ∑ w : W, dp.prior w = 1) :
    ∑ o : O, dp.cellProbability (Finset.univ.filter (classify · = o)) = 1 := by
  unfold DecisionProblem.cellProbability
  rw [Finset.sum_fiberwise_of_maps_to (fun w _ ↦ Finset.mem_univ (classify w))
    (fun w ↦ dp.prior w)]
  exact hsum

/-- Under the uniform prior, `priorMeasure` is the counting measure divided by `|W|`. -/
private lemma priorMeasure_uniform [MeasurableSpace W] [MeasurableSingletonClass W]
    (dp : DecisionProblem ℝ W A)
    (hprior : dp.prior = fun _ ↦ ((Fintype.card W : ℝ))⁻¹)
    (hW : (0 : ℝ) < Fintype.card W) :
    dp.priorMeasure = ((Fintype.card W : ℝ≥0∞))⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [priorMeasure_singleton, hprior, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one, ENNReal.ofReal_inv_of_pos hW, ENNReal.ofReal_natCast]

/-- When `F ∅ = 0`, the sum of `F` over the fibres of a classifier is the sum over its outputs,
since an empty fibre collapses in the image but contributes nothing. -/
private lemma sum_image_fibers_eq
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (classify : W → ι) (F : Finset W → R) (hF : F ∅ = 0) :
    (∑ cell ∈ (Finset.univ : Finset ι).image
        (fun o : ι ↦ Finset.univ.filter (classify · = o)), F cell) =
      ∑ o : ι, F (Finset.univ.filter (classify · = o)) := by
  classical
  refine Finset.sum_image_of_disjoint (I := Finset.univ)
    (f := fun o : ι ↦ Finset.univ.filter (classify · = o)) (g := F) ?_ ?_
  · show F ⊥ = 0
    rw [show (⊥ : Finset W) = ∅ from rfl, hF]
  · intro o₁ _ o₂ _ hne
    refine Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_
    have h₁ : classify w = o₁ := (Finset.mem_filter.mp hw₁).2
    have h₂ : classify w = o₂ := (Finset.mem_filter.mp hw₂).2
    exact hne (h₁.symm.trans h₂)

/-- When the cells are the fibres of a classifier, the expected utility value of the question
is `∑ₒ P(cell o) · V(D ∣ cell o) − V(D)`. -/
private lemma questionUtility_image_fibers_eq (dp : DecisionProblem ℝ W A)
    {acts : Finset A} {ι : Type*} [Fintype ι] [DecidableEq ι] (classify : W → ι)
    (_hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w : W, dp.prior w = 1) :
    dp.questionUtility acts (Finset.univ.image
        (fun o : ι ↦ Finset.univ.filter (classify · = o))) =
      (∑ o : ι, dp.cellProbability (Finset.univ.filter (classify · = o))
        * dp.condValue acts (Finset.univ.filter (classify · = o))) -
        dp.value acts := by
  classical
  have hcp1 : ∑ o : ι, dp.cellProbability (Finset.univ.filter (classify · = o)) = 1 :=
    cellProbability_sum_fibers dp classify hsum
  have hcp_empty : dp.cellProbability ∅ = 0 := by
    simp [DecisionProblem.cellProbability]
  unfold DecisionProblem.questionUtility
  have hcell_eq : ∀ cell : Finset W,
      dp.cellProbability cell * dp.utilityValue acts cell =
      dp.cellProbability cell * dp.condValue acts cell -
        dp.cellProbability cell * dp.value acts := fun _ ↦ by
    unfold DecisionProblem.utilityValue
    ring
  simp_rw [hcell_eq, Finset.sum_sub_distrib]
  rw [sum_image_fibers_eq classify
        (fun cell ↦ dp.cellProbability cell * dp.condValue acts cell)
        (by rw [hcp_empty, zero_mul]),
    sum_image_fibers_eq classify
        (fun cell ↦ dp.cellProbability cell * dp.value acts)
        (by rw [hcp_empty, zero_mul])]
  rw [← Finset.sum_mul, hcp1, one_mul]

/-- The integral of a function against the prior as a measure is its prior-weighted sum. -/
theorem integral_priorMeasure [MeasurableSpace W] [MeasurableSingletonClass W]
    (dp : DecisionProblem ℝ W A) (hprior : ∀ w, 0 ≤ dp.prior w) (g : W → ℝ) :
    ∫ w, g w ∂dp.priorMeasure = ∑ w, dp.prior w * g w := by
  rw [integral_fintype .of_finite]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [measureReal_def, priorMeasure_singleton, ENNReal.toReal_ofReal (hprior w), smul_eq_mul]

/-- The decision value of the prior is the value of the decision problem over all actions. -/
theorem decisionValue_priorMeasure [MeasurableSpace W] [MeasurableSingletonClass W] [Fintype A]
    [Nonempty A] (dp : DecisionProblem ℝ W A) (hprior : ∀ w, 0 ≤ dp.prior w) :
    decisionValue dp.utility dp.priorMeasure = dp.value Finset.univ := by
  rw [value_of_nonempty Finset.univ_nonempty, Finset.sup'_univ_eq_ciSup, decisionValue]
  simp only [integral_priorMeasure dp hprior, expectedUtility]

/-- The expected utility value of the question whose cells are the fibres of `f` is the value of
information of the experiment that observes `f`. -/
theorem valueOfInformation_deterministic [MeasurableSpace W] [DiscreteMeasurableSpace W]
    [Nonempty W] [Fintype A] [Nonempty A] [Fintype O] [DecidableEq O] [MeasurableSpace O]
    [MeasurableSingletonClass O] (dp : DecisionProblem ℝ W A) (hprior : ∀ w, 0 ≤ dp.prior w)
    (hsum : ∑ w, dp.prior w = 1) (f : W → O) :
    valueOfInformation (decisionValue dp.utility)
        (Kernel.deterministic f (measurable_of_countable f)) dp.priorMeasure =
      dp.questionUtility Finset.univ (Finset.univ.image fun o ↦ Finset.univ.filter (f · = o)) := by
  set κ := Kernel.deterministic f (measurable_of_countable f)
  have hcell (o : O) : (κ ∘ₘ dp.priorMeasure).real {o} *
      decisionValue dp.utility ((κ†dp.priorMeasure) o) =
        dp.cellProbability (Finset.univ.filter (f · = o)) *
          dp.condValue Finset.univ (Finset.univ.filter (f · = o)) := by
    rw [decisionValue, Real.mul_iSup_of_nonneg measureReal_nonneg,
      cellProbability_mul_condValue hprior Finset.univ_nonempty, Finset.sup'_univ_eq_ciSup]
    refine iSup_congr fun a ↦ ?_
    rw [comp_real_mul_integral_posterior, integral_priorMeasure dp hprior, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [measureReal_def, Kernel.deterministic_apply,
      Measure.dirac_apply' _ (measurableSet_singleton o)]
    by_cases h : f w = o <;> simp [h]
  rw [valueOfInformation, integral_fintype .of_finite, decisionValue_priorMeasure dp hprior,
    questionUtility_image_fibers_eq dp f hprior hsum]
  congr 1
  exact Finset.sum_congr rfl fun o _ ↦ hcell o

/-- If the partition of `g` is never more useful than that of `f` in a decision problem over
the action space `O'`, then `g` factors through `f`. -/
theorem factorsThrough_of_forall_questionUtility_le [Nonempty W] [MeasurableSpace W]
    [DiscreteMeasurableSpace W] [Fintype O] [DecidableEq O] [MeasurableSpace O]
    [MeasurableSingletonClass O] [Fintype O'] [DecidableEq O'] [MeasurableSpace O']
    [MeasurableSingletonClass O'] [Nonempty O'] (f : W → O) (g : W → O')
    (h : ∀ (dp : DecisionProblem ℝ W O'), (∀ w, 0 ≤ dp.prior w) →
      (∑ w : W, dp.prior w = 1) →
      dp.questionUtility Finset.univ (Finset.univ.image
          (fun o' : O' ↦ Finset.univ.filter (g · = o'))) ≤
        dp.questionUtility Finset.univ (Finset.univ.image
          (fun o : O ↦ Finset.univ.filter (f · = o)))) :
    ∃ ψ : O → O', g = ψ ∘ f := by
  have hcard : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  refine (Kernel.deterministic_isGarblingOf_deterministic_iff (measurable_of_countable f)
    (measurable_of_countable g)).1 (isGarblingOf_of_bayesRisk_uniform_le fun ℓ hℓ ↦ ?_)
  let dp : DecisionProblem ℝ W O' := ⟨fun w o' ↦ -(ℓ w o').toReal, fun _ ↦ (Fintype.card W : ℝ)⁻¹⟩
  have hprior : ∀ w, 0 ≤ dp.prior w := fun _ ↦ inv_nonneg.2 hcard.le
  have hsum : ∑ w, dp.prior w = 1 := by
    simp [dp, Finset.card_univ]
  have := dp.isProbabilityMeasure_priorMeasure hprior hsum
  have hU : ∀ w o', dp.utility w o' ≤ 0 := fun _ _ ↦ neg_nonpos.2 ENNReal.toReal_nonneg
  have hℓ' : ℓ = fun w o' ↦ ENNReal.ofReal (0 - dp.utility w o') := by
    ext w o'
    simp [dp, ENNReal.ofReal_toReal (hℓ w o')]
  rw [← priorMeasure_uniform dp rfl hcard, hℓ', bayesRisk_ofReal_sub hU, bayesRisk_ofReal_sub hU]
  refine ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ 0)
  have hf := valueOfInformation_deterministic dp hprior hsum f
  have hg := valueOfInformation_deterministic dp hprior hsum g
  rw [valueOfInformation] at hf hg
  linarith [h dp hprior hsum]

/-! ### Partitions -/

/-- The fibres of the block map of a partition are its parts and the empty fibre. -/
private theorem image_filter_part (P : Finpartition (Finset.univ : Finset W)) :
    Finset.univ.image (fun c ↦ Finset.univ.filter (P.part · = c)) = insert ∅ P.parts := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨d, rfl⟩
    by_cases hd : d ∈ P.parts
    · exact .inr (by convert hd using 1; ext v; simp [P.part_eq_iff_mem hd])
    · exact .inl (Finset.filter_eq_empty_iff.2 fun v _ h ↦
        hd (h ▸ P.part_mem.2 (Finset.mem_univ v)))
  · rintro (rfl | hc)
    · exact ⟨∅, Finset.filter_eq_empty_iff.2 fun v _ h ↦
        P.ne_bot (P.part_mem.2 (Finset.mem_univ v)) (by simp at h)⟩
    · exact ⟨c, by ext v; simp [P.part_eq_iff_mem hc]⟩

private theorem questionUtility_insert_empty (dp : DecisionProblem ℝ W A) (acts : Finset A)
    (cells : Finset (Finset W)) :
    dp.questionUtility acts (insert ∅ cells) = dp.questionUtility acts cells := by
  by_cases h : ∅ ∈ cells
  · rw [Finset.insert_eq_of_mem h]
  · rw [questionUtility, Finset.sum_insert h]
    simp [cellProbability, questionUtility]

/-- One partition refines another exactly when it is at least as useful in every decision
problem with a probability prior. -/
theorem le_iff_forall_questionUtility_le (P Q : Finpartition (Finset.univ : Finset W)) :
    P ≤ Q ↔ ∀ {A : Type u} (dp : DecisionProblem ℝ W A) (acts : Finset A),
      (∀ w, 0 ≤ dp.prior w) → ∑ w, dp.prior w = 1 →
        dp.questionUtility acts Q.parts ≤ dp.questionUtility acts P.parts := by
  refine ⟨fun h _ dp acts hprior _ ↦ questionUtility_anti_of_le dp acts h hprior, fun h ↦ ?_⟩
  rcases isEmpty_or_nonempty W with hW | hW
  · exact fun b hb ↦ isEmptyElim (P.nonempty_of_mem_parts hb).choose
  let _ : MeasurableSpace W := ⊤
  let _ : MeasurableSpace (Finset W) := ⊤
  have : DiscreteMeasurableSpace W := ⟨fun _ ↦ trivial⟩
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  obtain ⟨ψ, hψ⟩ := factorsThrough_of_forall_questionUtility_le P.part Q.part
    fun dp hprior hsum ↦ by
      simpa only [image_filter_part, questionUtility_insert_empty] using
        h dp Finset.univ hprior hsum
  exact Finpartition.le_iff_factorsThrough_part.2 fun a b hab ↦ by simp [hψ, hab]

end Core.DecisionTheory.DecisionProblem
