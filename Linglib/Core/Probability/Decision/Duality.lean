/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Probability.Decision.Blackwell
import Linglib.Core.Probability.Decision.Basic

/-!
# Utility–loss duality for finite decision problems

The bridge between [van-rooy-2003]'s utility scale (`DecisionProblem`,
`questionUtility` over ℝ) and mathlib's loss scale
(`ProbabilityTheory.bayesRisk` over `ℝ≥0∞`): for a bound `C` above every
utility, the Bayes risk of the partition experiment under the regret loss
`C − U` equals `C` minus the partition's decision value
(`bayesRisk_deterministic_regretLoss`). Through it, [van-rooy-2003]'s §4.1
Fact becomes a *biconditional* theorem about the Blackwell order:

* forward (`questionUtility_comp_le`): coarsening the classifier cannot raise
  question utility — the partition instance of the data-processing inequality
  `bayesRisk_deterministic_le_deterministic_comp`;
* converse (`factorsThrough_of_forall_questionUtility_le`): a partition whose
  question utility is dominated in *every* decision problem factors through
  the dominating one — the Blackwell–Sherman–Stein converse
  (`isGarblingOf_of_blackwellDominates`) plus the deterministic factoring
  characterization (`Kernel.deterministic_isGarblingOf_deterministic_iff`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Core.DecisionTheory.DecisionProblem

variable {W A O O' : Type*} [Fintype W] [DecidableEq W]

/-- The prior of a decision problem as a measure: the weighted sum of Dirac
masses `∑ w, ofReal (prior w) • δ_w`. -/
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
  rw [Finset.sum_ite_eq' Finset.univ w fun w' => ENNReal.ofReal (dp.prior w')]
  simp

instance [MeasurableSpace W] (dp : DecisionProblem ℝ W A) :
    IsFiniteMeasure dp.priorMeasure := by
  refine ⟨?_⟩
  show (∑ w : W, ENNReal.ofReal (dp.prior w) • Measure.dirac w) Set.univ < ⊤
  rw [Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.2 fun w _ => ?_
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
  rw [← ENNReal.ofReal_sum_of_nonneg fun w _ => hprior w, hsum, ENNReal.ofReal_one]

/-- The regret loss at bound `C`: `ℓ(w, a) = C − U(w, a)`, clamped into
`ℝ≥0∞`. For `C` above every utility this is the order-reversing change of
scale between utilities and losses. -/
noncomputable def regretLoss (dp : DecisionProblem ℝ W A) (C : ℝ) :
    W → A → ℝ≥0∞ :=
  λ w a => ENNReal.ofReal (C - dp.utility w a)

/-- Finite subtypes of actions carry the discrete σ-algebra. -/
scoped instance (acts : Finset A) : MeasurableSpace acts := ⊤

scoped instance (acts : Finset A) : MeasurableSingletonClass acts :=
  ⟨λ _ => trivial⟩

omit [Fintype W] [DecidableEq W] in
/-- `P(cell)·V(D∣cell) = max_{a ∈ acts} ∑_{w ∈ cell} P(w)·U(w,a)`: the
probability-weighted conditional value equals the unnormalized best-action value
on the cell. Local specialisation of the private lemma in
`Core.Probability.Decision.Basic`, restated at `K := ℝ` with an explicit
nonempty-action hypothesis. -/
private lemma cellProbability_mul_condValue_sup' (dp : DecisionProblem ℝ W A)
    {acts : Finset A} (hacts : acts.Nonempty) (cell : Finset W)
    (hprior : ∀ w, 0 ≤ dp.prior w) :
    dp.cellProbability cell * dp.condValue acts cell =
      acts.sup' hacts (fun a => ∑ w ∈ cell, dp.prior w * dp.utility w a) := by
  rw [condValue_of_nonempty hacts]
  have htp_nonneg : 0 ≤ dp.cellProbability cell :=
    Finset.sum_nonneg fun w _ => hprior w
  by_cases htp : dp.cellProbability cell = 0
  · have hS : cell.sum dp.prior = 0 := htp
    rw [htp, zero_mul]
    have hpw : ∀ w ∈ cell, dp.prior w = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hprior w).mp hS
    exact (Finset.sup'_eq_of_forall (s := acts) (H := hacts) (a := (0 : ℝ))
      (f := fun a => ∑ w ∈ cell, dp.prior w * dp.utility w a)
      (fun a _ => Finset.sum_eq_zero
        fun w hw => by rw [hpw w hw, zero_mul])).symm
  · have hS : cell.sum dp.prior ≠ 0 := htp
    rw [Finset.mul₀_sup' htp_nonneg _ acts hacts]
    refine Finset.sup'_congr hacts rfl fun a _ => ?_
    show cell.sum dp.prior * dp.condExpectedUtility cell a
        = ∑ w ∈ cell, dp.prior w * dp.utility w a
    rw [condExpectedUtility_of_ne_zero hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hS]

/-- **Utility–loss duality**: for a classifier `classify : W → O`, the Bayes
risk of the deterministic experiment "observe the cell of `w`" under the
regret loss at `C`, with actions restricted to `acts`, is `C` minus the
partition's decision value `∑_o P(o)·V(D ∣ fiber o)`. The optimal estimator
is best-action-per-cell, and mathlib's `bayesRisk` and [van-rooy-2003]'s
conditional value compute the same quantity on opposite scales. -/
theorem bayesRisk_deterministic_regretLoss [MeasurableSpace W]
    [MeasurableSingletonClass W] [Fintype O] [DecidableEq O] [MeasurableSpace O]
    [MeasurableSingletonClass O] (dp : DecisionProblem ℝ W A)
    {acts : Finset A} (hacts : acts.Nonempty) (classify : W → O)
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w : W, dp.prior w = 1)
    {C : ℝ} (hC : ∀ w, ∀ a ∈ acts, dp.utility w a ≤ C) :
    bayesRisk (λ w (a : acts) => dp.regretLoss C w a)
        (Kernel.deterministic classify (measurable_of_countable classify))
        dp.priorMeasure
      = ENNReal.ofReal (C - ∑ o : O,
          dp.cellProbability (Finset.univ.filter (classify · = o)) *
            dp.condValue acts (Finset.univ.filter (classify · = o))) := by
  classical
  haveI : Nonempty acts := hacts.to_subtype
  set fiber : O → Finset W := fun o => Finset.univ.filter (classify · = o)
    with hfiber_def
  set uSum : Finset W → A → ℝ :=
    fun cell a => ∑ w ∈ cell, dp.prior w * dp.utility w a with huSum_def
  -- Bound above every action inside the cell, per the loss's bound `C`.
  have hcond_le : ∀ (cell : Finset W) (a : A), a ∈ acts →
      uSum cell a ≤ C * dp.cellProbability cell := by
    intro cell a ha
    unfold DecisionProblem.cellProbability
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC w a ha) (hprior w)
  -- Cell inner sum: ENNReal expresses a nonnegative real.
  have inner_eq : ∀ (cell : Finset W) (a : ↥acts),
      ∑ w ∈ cell, dp.priorMeasure {w} * dp.regretLoss C w a
        = ENNReal.ofReal (C * dp.cellProbability cell - uSum cell a.val) := by
    intro cell a
    have hnn : ∀ w ∈ cell, 0 ≤ dp.prior w * (C - dp.utility w a.val) := fun w _ =>
      mul_nonneg (hprior w) (sub_nonneg.mpr (hC w a.val a.property))
    have hsum_eq :
        ∑ w ∈ cell, dp.prior w * (C - dp.utility w a.val)
          = C * dp.cellProbability cell - uSum cell a.val := by
      unfold DecisionProblem.cellProbability
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hpt : ∀ w, dp.priorMeasure {w} * dp.regretLoss C w a
        = ENNReal.ofReal (dp.prior w * (C - dp.utility w a.val)) := fun w => by
      simp only [priorMeasure_singleton, regretLoss]
      rw [← ENNReal.ofReal_mul (hprior w)]
    calc ∑ w ∈ cell, dp.priorMeasure {w} * dp.regretLoss C w a
        = ∑ w ∈ cell, ENNReal.ofReal (dp.prior w * (C - dp.utility w a.val)) :=
          Finset.sum_congr rfl fun w _ => hpt w
      _ = ENNReal.ofReal (∑ w ∈ cell, dp.prior w * (C - dp.utility w a.val)) :=
          (ENNReal.ofReal_sum_of_nonneg hnn).symm
      _ = ENNReal.ofReal (C * dp.cellProbability cell - uSum cell a.val) := by rw [hsum_eq]
  -- Per-cell: the ⨅ over `acts` of the inner sum collapses to the sup' identity.
  have per_cell : ∀ o : O,
      ⨅ (a : ↥acts),
          ∑ w ∈ fiber o, dp.priorMeasure {w} * dp.regretLoss C w a
        = ENNReal.ofReal (C * dp.cellProbability (fiber o)
            - dp.cellProbability (fiber o) * dp.condValue acts (fiber o)) := by
    intro o
    -- Rewrite each inner sum, then collapse the ⨅ through `ofReal`.
    simp_rw [inner_eq]
    rw [← ENNReal.ofReal_iInf (fun a : ↥acts =>
          C * dp.cellProbability (fiber o) - uSum (fiber o) a.val),
      cellProbability_mul_condValue_sup' dp hacts (fiber o) hprior]
    congr 1
    rw [← Finset.inf'_univ_eq_ciInf
      (f := fun a : ↥acts => C * dp.cellProbability (fiber o) - uSum (fiber o) a.val)]
    refine le_antisymm ?_ ?_
    · obtain ⟨a, ha, ha_eq⟩ := Finset.exists_mem_eq_sup' hacts (uSum (fiber o))
      refine (Finset.inf'_le
        (f := fun a : ↥acts => C * dp.cellProbability (fiber o) - uSum (fiber o) a.val)
        (Finset.mem_univ (⟨a, ha⟩ : ↥acts))).trans ?_
      show C * dp.cellProbability (fiber o) - uSum (fiber o) a
        ≤ C * dp.cellProbability (fiber o) - acts.sup' hacts (uSum (fiber o))
      rw [← ha_eq]
    · refine Finset.le_inf' _ _ fun a _ => ?_
      have hle : uSum (fiber o) a.val ≤ acts.sup' hacts (uSum (fiber o)) :=
        Finset.le_sup' _ a.property
      linarith
  -- Cell probabilities sum to `1` via the fiber partition.
  have hcp_sum : ∑ o : O, dp.cellProbability (fiber o) = 1 := by
    unfold DecisionProblem.cellProbability
    rw [Finset.sum_fiberwise_of_maps_to (fun w _ => Finset.mem_univ (classify w))
      (fun w => dp.prior w)]
    exact hsum
  -- The per-cell values are nonnegative, allowing `ofReal` to pull outside the sum.
  have hcell_nn : ∀ o : O, 0 ≤
      C * dp.cellProbability (fiber o)
        - dp.cellProbability (fiber o) * dp.condValue acts (fiber o) := fun o => by
    have := cellProbability_mul_condValue_sup' dp hacts (fiber o) hprior
    have hsup_le : acts.sup' hacts (uSum (fiber o)) ≤ C * dp.cellProbability (fiber o) :=
      Finset.sup'_le hacts _ fun a ha => hcond_le (fiber o) a ha
    linarith
  -- Assemble.
  rw [bayesRisk_deterministic (measurable_of_countable classify) _ _]
  show ∑ o : O, ⨅ (a : ↥acts),
        ∑ w ∈ fiber o, dp.priorMeasure {w} * dp.regretLoss C w a
      = ENNReal.ofReal (C - ∑ o : O,
          dp.cellProbability (fiber o) * dp.condValue acts (fiber o))
  simp_rw [per_cell]
  rw [← ENNReal.ofReal_sum_of_nonneg fun o _ => hcell_nn o]
  congr 1
  calc ∑ o : O, (C * dp.cellProbability (fiber o)
              - dp.cellProbability (fiber o) * dp.condValue acts (fiber o))
      = C * ∑ o : O, dp.cellProbability (fiber o)
          - ∑ o : O, dp.cellProbability (fiber o) * dp.condValue acts (fiber o) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = C - ∑ o : O, dp.cellProbability (fiber o) * dp.condValue acts (fiber o) := by
        rw [hcp_sum, mul_one]

omit [DecidableEq W] in
/-- The **partition of a classifier** on `Finset.univ` as an image: cells
indexed by outputs, kept faithful by the fiber-nonempty hypothesis. -/
private lemma cellProbability_sum_fibers (dp : DecisionProblem ℝ W A)
    {O : Type*} [Fintype O] [DecidableEq O] (classify : W → O)
    (hsum : ∑ w : W, dp.prior w = 1) :
    ∑ o : O, dp.cellProbability (Finset.univ.filter (classify · = o)) = 1 := by
  unfold DecisionProblem.cellProbability
  rw [Finset.sum_fiberwise_of_maps_to (fun w _ => Finset.mem_univ (classify w))
    (fun w => dp.prior w)]
  exact hsum

omit [DecidableEq W] in
/-- The Bayes risk of a deterministic experiment at a finite-valued loss and the
uniform-prior decision problem's `priorMeasure` equals `ofReal` of `-∑ cellProb·condValue`
under the utility `-(ℓ).toReal`. Extracted to a private lemma so its universe (`ι`) can
be pinned independently at each call site (for `f : W → O` and `g : W → O'`). -/
private lemma bayesRisk_deterministic_toReal_utility
    [MeasurableSpace W] [MeasurableSingletonClass W]
    {O' : Type*} [Fintype O'] [DecidableEq O']
    [MeasurableSpace O'] [MeasurableSingletonClass O'] [Nonempty O']
    (ℓ : W → O' → ℝ≥0∞) (hℓ_fin : ∀ w o', ℓ w o' ≠ ⊤)
    (dp : DecisionProblem ℝ W O')
    (hdp_prior_val : ∀ w, dp.prior w = ((Fintype.card W : ℝ))⁻¹)
    (hdp_prior : ∀ w, 0 ≤ dp.prior w)
    (hutil : ∀ w o', dp.utility w o' = -(ℓ w o').toReal)
    (hpm_pt : ∀ w, dp.priorMeasure {w} = ENNReal.ofReal ((Fintype.card W : ℝ))⁻¹)
    (hcardR : (0 : ℝ) < Fintype.card W)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (classifier : W → ι) :
    bayesRisk ℓ (Kernel.deterministic classifier (measurable_of_countable classifier))
        dp.priorMeasure =
      ENNReal.ofReal (- ∑ o : ι, dp.cellProbability
        (Finset.univ.filter (classifier · = o))
          * dp.condValue Finset.univ
        (Finset.univ.filter (classifier · = o))) := by
  classical
  haveI : IsFiniteMeasure dp.priorMeasure := inferInstance
  rw [bayesRisk_deterministic (measurable_of_countable classifier) ℓ dp.priorMeasure]
  have hℓ_pt : ∀ w o', ℓ w o' = ENNReal.ofReal ((ℓ w o').toReal) := fun w o' =>
    (ENNReal.ofReal_toReal (hℓ_fin w o')).symm
  have h_inner_eq : ∀ (o : ι) (o' : O'),
      (∑ w ∈ Finset.univ.filter (classifier · = o), dp.priorMeasure {w} * ℓ w o') =
      ENNReal.ofReal
        (∑ w ∈ Finset.univ.filter (classifier · = o),
          (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal) := by
    intro o o'
    rw [ENNReal.ofReal_sum_of_nonneg fun w _ =>
      mul_nonneg (inv_nonneg.mpr hcardR.le) ENNReal.toReal_nonneg]
    refine Finset.sum_congr rfl fun w _ => ?_
    conv_lhs => rw [hpm_pt w, hℓ_pt w o',
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hcardR.le)]
  simp_rw [h_inner_eq]
  have h_iInf : ∀ o : ι, ⨅ o' : O', ENNReal.ofReal
        (∑ w ∈ Finset.univ.filter (classifier · = o),
          (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal) =
      ENNReal.ofReal (⨅ o' : O',
        ∑ w ∈ Finset.univ.filter (classifier · = o),
          (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal) := fun o =>
    (ENNReal.ofReal_iInf _).symm
  simp_rw [h_iInf]
  have h_iInf_nn : ∀ o : ι, 0 ≤ ⨅ o' : O',
      ∑ w ∈ Finset.univ.filter (classifier · = o),
        (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal := fun o => by
    refine le_ciInf fun _ => ?_
    exact Finset.sum_nonneg fun w _ =>
      mul_nonneg (inv_nonneg.mpr hcardR.le) ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_sum_of_nonneg fun o _ => h_iInf_nn o]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  set cell : Finset W := Finset.univ.filter (classifier · = o)
  have hlink : ∀ o' : O',
      ∑ w ∈ cell, (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal =
        -(∑ w ∈ cell, dp.prior w * dp.utility w o') := by
    intro o'
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hutil w o', hdp_prior_val w]
    show (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal =
      -((Fintype.card W : ℝ)⁻¹ * -(ℓ w o').toReal)
    ring
  calc (⨅ o' : O', ∑ w ∈ cell,
            (Fintype.card W : ℝ)⁻¹ * (ℓ w o').toReal)
      = ⨅ o' : O', -(∑ w ∈ cell, dp.prior w * dp.utility w o') := by
        simp_rw [hlink]
    _ = (Finset.univ : Finset O').inf' Finset.univ_nonempty
          (fun o' : O' => -(∑ w ∈ cell, dp.prior w * dp.utility w o')) := by
        rw [← Finset.inf'_univ_eq_ciInf]
    _ = -Finset.univ.sup' Finset.univ_nonempty
          (fun o' : O' => ∑ w ∈ cell, dp.prior w * dp.utility w o') := by
        refine le_antisymm ?_ ?_
        · obtain ⟨o'_max, _, hmax⟩ :=
            Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset O'))
              Finset.univ_nonempty
              (fun o' : O' => ∑ w ∈ cell, dp.prior w * dp.utility w o')
          have := Finset.inf'_le (s := (Finset.univ : Finset O'))
            (f := fun o' : O' => -(∑ w ∈ cell, dp.prior w * dp.utility w o'))
            (Finset.mem_univ o'_max)
          linarith [hmax]
        · refine Finset.le_inf' _ _ fun o' _ => ?_
          have := Finset.le_sup' (s := (Finset.univ : Finset O'))
            (f := fun o' : O' => ∑ w ∈ cell, dp.prior w * dp.utility w o')
            (Finset.mem_univ o')
          linarith
    _ = -(dp.cellProbability cell * dp.condValue Finset.univ cell) := by
        rw [cellProbability_mul_condValue_sup' dp Finset.univ_nonempty cell hdp_prior]

omit [DecidableEq W] in
/-- With all fibers nonempty, the fiber map `o ↦ classify⁻¹ o` is injective on
`Finset.univ`, so `Finset.sum_image` reduces the image sum to an `O`-indexed
sum. -/
private lemma fiberMap_injOn {O : Type*} [Fintype O] [DecidableEq O]
    (classify : W → O)
    (hfib : ∀ o : O, (Finset.univ.filter (classify · = o)).Nonempty) :
    Set.InjOn (fun o : O => Finset.univ.filter (classify · = o))
      (Finset.univ : Finset O) := fun o₁ _ o₂ _ heq => by
  obtain ⟨w, hw⟩ := hfib o₁
  have hw₁ : classify w = o₁ := (Finset.mem_filter.mp hw).2
  have hw₂ : w ∈ Finset.univ.filter (classify · = o₂) := by
    show w ∈ (fun o => Finset.univ.filter (classify · = o)) o₂
    rw [← heq]; exact hw
  exact hw₁.symm.trans (Finset.mem_filter.mp hw₂).2

/-- `EUV(Q) = ∑_i P(cell_i)·V(D|cell_i) − V(D)` when the cells are the fibers of
an injective indexing map summing to full prior mass. Reduces the image-indexed
`questionUtility` to an indexer-side sum, then splits off the constant baseline. -/
private lemma questionUtility_image_eq_sum_sub (dp : DecisionProblem ℝ W A)
    {acts : Finset A} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cm : ι → Finset W) (hinj : Set.InjOn cm (Finset.univ : Finset ι))
    (hcp1 : ∑ i : ι, dp.cellProbability (cm i) = 1) :
    dp.questionUtility acts (Finset.univ.image cm) =
      (∑ i : ι, dp.cellProbability (cm i) * dp.condValue acts (cm i)) -
        dp.value acts := by
  unfold DecisionProblem.questionUtility
  rw [Finset.sum_image hinj]
  simp only [DecisionProblem.utilityValue, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hcp1, one_mul]

/-- **[van-rooy-2003] §4.1, forward direction, from the Blackwell order**:
coarsening the classifier by post-composition cannot raise question utility.
The partition instance of `bayesRisk_deterministic_le_deterministic_comp`,
transported along the duality. -/
theorem questionUtility_comp_le [MeasurableSpace W] [MeasurableSingletonClass W]
    [Fintype O] [DecidableEq O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [Fintype O'] [DecidableEq O'] [MeasurableSpace O'] [MeasurableSingletonClass O']
    (dp : DecisionProblem ℝ W A) {acts : Finset A} (hacts : acts.Nonempty)
    (classify : W → O) (ψ : O → O')
    (hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w : W, dp.prior w = 1)
    (hfib : ∀ o : O, (Finset.univ.filter (classify · = o)).Nonempty)
    (hfib' : ∀ o' : O', (Finset.univ.filter (λ w => ψ (classify w) = o')).Nonempty) :
    dp.questionUtility acts (Finset.univ.image
        (λ o' : O' => Finset.univ.filter (λ w => ψ (classify w) = o'))) ≤
      dp.questionUtility acts (Finset.univ.image
        (λ o : O => Finset.univ.filter (classify · = o))) := by
  classical
  -- `Nonempty W`, else `hsum` says `0 = 1`.
  have hW : Nonempty W := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Finset.univ_eq_empty] at hsum
  -- A bound `C ≥ 0` above every utility on `W × acts`.
  set pairs : Finset (W × A) := Finset.univ ×ˢ acts
  have hpne : pairs.Nonempty := by
    obtain ⟨w⟩ := hW
    obtain ⟨a, ha⟩ := hacts
    exact ⟨(w, a), Finset.mem_product.mpr ⟨Finset.mem_univ w, ha⟩⟩
  set C₀ : ℝ := pairs.sup' hpne (fun p => dp.utility p.1 p.2)
  set C : ℝ := max 0 C₀
  have hC_nn : 0 ≤ C := le_max_left _ _
  have hC : ∀ w, ∀ a ∈ acts, dp.utility w a ≤ C := fun w a ha =>
    (Finset.le_sup' (s := pairs) (b := (w, a))
        (fun p : W × A => dp.utility p.1 p.2)
        (Finset.mem_product.mpr ⟨Finset.mem_univ w, ha⟩)).trans
      (le_max_right _ _)
  -- Rewrite both `questionUtility` sides.
  set fineMap : O → Finset W := fun o => Finset.univ.filter (classify · = o)
  set coarseMap : O' → Finset W := fun o' =>
    Finset.univ.filter (fun w => ψ (classify w) = o')
  have hfine_inj : Set.InjOn fineMap (Finset.univ : Finset O) :=
    fiberMap_injOn classify hfib
  have hcoarse_inj : Set.InjOn coarseMap (Finset.univ : Finset O') :=
    fiberMap_injOn (fun w => ψ (classify w)) hfib'
  have hfine_cp1 := cellProbability_sum_fibers dp classify hsum
  have hcoarse_cp1 := cellProbability_sum_fibers dp (fun w => ψ (classify w)) hsum
  rw [questionUtility_image_eq_sum_sub dp coarseMap hcoarse_inj hcoarse_cp1,
    questionUtility_image_eq_sum_sub dp fineMap hfine_inj hfine_cp1]
  -- Every `condValue acts cm` is bounded above by `C`.
  have hval_le_C : ∀ (cm : Finset W), dp.condValue acts cm ≤ C := fun cm => by
    rw [condValue_of_nonempty hacts]
    refine Finset.sup'_le hacts _ fun a ha => ?_
    by_cases h0 : cm.sum dp.prior = 0
    · rw [show dp.condExpectedUtility cm a = 0 from
        condExpectedUtility_of_eq_zero h0 a]
      exact hC_nn
    · rw [condExpectedUtility_of_ne_zero h0]
      have hcp_pos : 0 < cm.sum dp.prior :=
        lt_of_le_of_ne (Finset.sum_nonneg fun w _ => hprior w) (Ne.symm h0)
      have hbound : ∑ w ∈ cm, dp.prior w / cm.sum dp.prior * dp.utility w a
          ≤ ∑ w ∈ cm, dp.prior w / cm.sum dp.prior * C := by
        refine Finset.sum_le_sum fun w _ => ?_
        exact mul_le_mul_of_nonneg_left (hC w a ha)
          (div_nonneg (hprior w) hcp_pos.le)
      have hsum_div : ∑ w ∈ cm, dp.prior w / cm.sum dp.prior * C = C := by
        have h1 : ∀ w : W, dp.prior w / cm.sum dp.prior * C
            = dp.prior w * (C / cm.sum dp.prior) := fun _ => by ring
        simp_rw [h1]
        rw [← Finset.sum_mul]
        exact mul_div_cancel₀ C h0
      linarith
  have hcp_nn : ∀ cm : Finset W, 0 ≤ dp.cellProbability cm := fun cm =>
    Finset.sum_nonneg fun w _ => hprior w
  -- Bounds on the total cell-probability × condValue sums.
  have hfineSum_le : (∑ o : O, dp.cellProbability (fineMap o) *
        dp.condValue acts (fineMap o)) ≤ C := by
    have hle : (∑ o : O, dp.cellProbability (fineMap o) *
        dp.condValue acts (fineMap o)) ≤
        ∑ o : O, dp.cellProbability (fineMap o) * C :=
      Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hval_le_C _) (hcp_nn _)
    have hCsum : (∑ o : O, dp.cellProbability (fineMap o) * C) = C := by
      rw [← Finset.sum_mul, hfine_cp1, one_mul]
    linarith
  have hcoarseSum_le : (∑ o' : O', dp.cellProbability (coarseMap o') *
        dp.condValue acts (coarseMap o')) ≤ C := by
    have hle : (∑ o' : O', dp.cellProbability (coarseMap o') *
        dp.condValue acts (coarseMap o')) ≤
        ∑ o' : O', dp.cellProbability (coarseMap o') * C :=
      Finset.sum_le_sum fun o' _ =>
        mul_le_mul_of_nonneg_left (hval_le_C _) (hcp_nn _)
    have hCsum : (∑ o' : O', dp.cellProbability (coarseMap o') * C) = C := by
      rw [← Finset.sum_mul, hcoarse_cp1, one_mul]
    linarith
  -- Apply the Blackwell DPI on the deterministic experiments, at the regret loss with `C`.
  -- We use `bayesRisk_le_bayesRisk_map` (universe-flexible) plus `deterministic_comp_eq_map`
  -- to bridge to `deterministic (ψ ∘ classify)`.
  have hmap_eq :
      (Kernel.deterministic classify (measurable_of_countable classify)).map ψ =
        Kernel.deterministic (ψ ∘ classify)
          ((measurable_of_countable ψ).comp (measurable_of_countable classify)) := by
    rw [← Kernel.deterministic_comp_eq_map (measurable_of_countable ψ),
      Kernel.deterministic_comp_deterministic]
  have hDPI :
      bayesRisk (fun w (a : ↥acts) => dp.regretLoss C w a)
          (Kernel.deterministic classify (measurable_of_countable classify))
          dp.priorMeasure ≤
        bayesRisk (fun w (a : ↥acts) => dp.regretLoss C w a)
          (Kernel.deterministic (ψ ∘ classify)
            ((measurable_of_countable ψ).comp (measurable_of_countable classify)))
          dp.priorMeasure := by
    rw [← hmap_eq]
    exact bayesRisk_le_bayesRisk_map _ _ _ (measurable_of_countable ψ)
  rw [bayesRisk_deterministic_regretLoss (dp := dp) hacts classify hprior hsum hC,
    bayesRisk_deterministic_regretLoss (dp := dp) hacts (ψ ∘ classify)
      hprior hsum hC] at hDPI
  simp only [Function.comp_apply] at hDPI
  -- Strip `ofReal` (RHS-side nonneg from `hcoarseSum_le`), rearrange, conclude.
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hDPI
  linarith

/-- The uniform-prior decision problem's `priorMeasure` is `Measure.count / |W|`. -/
private lemma priorMeasure_uniform [MeasurableSpace W] [MeasurableSingletonClass W]
    (dp : DecisionProblem ℝ W A)
    (hprior : dp.prior = fun _ => ((Fintype.card W : ℝ))⁻¹)
    (hW : (0 : ℝ) < Fintype.card W) :
    dp.priorMeasure = ((Fintype.card W : ℝ≥0∞))⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton fun w => ?_
  rw [priorMeasure_singleton, hprior, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one, ENNReal.ofReal_inv_of_pos hW, ENNReal.ofReal_natCast]

/-- Sum of `F cell` over the image of a fiber map equals the domain-indexed sum
`∑ o, F (fiber o)`, provided `F ∅ = 0` (empty fibers collapse in the image but
contribute zero). -/
private lemma sum_image_fibers_eq
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid R]
    (classify : W → ι) (F : Finset W → R) (hF : F ∅ = 0) :
    (∑ cell ∈ (Finset.univ : Finset ι).image
        (fun o : ι => Finset.univ.filter (classify · = o)), F cell) =
      ∑ o : ι, F (Finset.univ.filter (classify · = o)) := by
  classical
  refine Finset.sum_image_of_disjoint (I := Finset.univ)
    (f := fun o : ι => Finset.univ.filter (classify · = o)) (g := F) ?_ ?_
  · show F ⊥ = 0
    rw [show (⊥ : Finset W) = ∅ from rfl, hF]
  · intro o₁ _ o₂ _ hne
    refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
    have h₁ : classify w = o₁ := (Finset.mem_filter.mp hw₁).2
    have h₂ : classify w = o₂ := (Finset.mem_filter.mp hw₂).2
    exact hne (h₁.symm.trans h₂)

/-- `EUV(Q) = ∑_i P(cell_i)·V(D|cell_i) − V(D)` when the cells are the fibers of a
classifier — a version of `questionUtility_image_eq_sum_sub` that does *not* require
nonempty fibers, since `cellProbability ∅ * X = 0` absorbs the collapsed empty cell. -/
private lemma questionUtility_image_fibers_eq (dp : DecisionProblem ℝ W A)
    {acts : Finset A} {ι : Type*} [Fintype ι] [DecidableEq ι] (classify : W → ι)
    (_hprior : ∀ w, 0 ≤ dp.prior w) (hsum : ∑ w : W, dp.prior w = 1) :
    dp.questionUtility acts (Finset.univ.image
        (fun o : ι => Finset.univ.filter (classify · = o))) =
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
        dp.cellProbability cell * dp.value acts := fun _ => by
    unfold DecisionProblem.utilityValue
    ring
  simp_rw [hcell_eq, Finset.sum_sub_distrib]
  rw [sum_image_fibers_eq classify
        (fun cell => dp.cellProbability cell * dp.condValue acts cell)
        (by rw [hcp_empty, zero_mul]),
    sum_image_fibers_eq classify
        (fun cell => dp.cellProbability cell * dp.value acts)
        (by rw [hcp_empty, zero_mul])]
  rw [← Finset.sum_mul, hcp1, one_mul]

/-- **[van-rooy-2003] §4.1, converse direction (Blackwell–Sherman–Stein)**:
if the partition of `g` has question utility dominated by that of `f` in
*every* decision problem over action space `O'`, then `g` factors through
`f` — the coarse question is genuinely a coarsening. Chains the utility–loss
duality against `isGarblingOf_of_bayesRisk_uniform_le` (only finite losses at the
uniform prior are needed) and the deterministic-factoring characterization
`Kernel.deterministic_isGarblingOf_deterministic_iff`. -/
theorem factorsThrough_of_forall_questionUtility_le [Nonempty W]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    [Fintype O] [DecidableEq O] [MeasurableSpace O] [MeasurableSingletonClass O]
    [Fintype O'] [DecidableEq O'] [MeasurableSpace O'] [MeasurableSingletonClass O']
    [Nonempty O'] (f : W → O) (g : W → O')
    (h : ∀ (dp : DecisionProblem ℝ W O'), (∀ w, 0 ≤ dp.prior w) →
      (∑ w : W, dp.prior w = 1) →
      dp.questionUtility Finset.univ (Finset.univ.image
          (λ o' : O' => Finset.univ.filter (g · = o'))) ≤
        dp.questionUtility Finset.univ (Finset.univ.image
          (λ o : O => Finset.univ.filter (f · = o)))) :
    ∃ ψ : O → O', g = ψ ∘ f := by
  classical
  have hcardR : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hcardR_ne : (Fintype.card W : ℝ) ≠ 0 := ne_of_gt hcardR
  suffices hgar :
      (Kernel.deterministic g (measurable_of_countable g)).IsGarblingOf
        (Kernel.deterministic f (measurable_of_countable f)) by
    exact (Kernel.deterministic_isGarblingOf_deterministic_iff
      (measurable_of_countable f) (measurable_of_countable g)).mp hgar
  refine _root_.ProbabilityTheory.isGarblingOf_of_bayesRisk_uniform_le ?_
  intro ℓ hℓ_fin
  -- Construct dp with utility = -(ℓ w o').toReal and uniform prior.
  let dp : DecisionProblem ℝ W O' :=
    { utility := fun w o' => -(ℓ w o').toReal
      prior := fun _ => ((Fintype.card W : ℝ))⁻¹ }
  have hdp_prior : ∀ w, 0 ≤ dp.prior w := fun _ => inv_nonneg.mpr hcardR.le
  have hdp_sum : ∑ w : W, dp.prior w = 1 := by
    show ∑ _ : W, ((Fintype.card W : ℝ))⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ hcardR_ne]
  have hdp_priorMeasure :
      dp.priorMeasure = ((Fintype.card W : ℝ≥0∞))⁻¹ • Measure.count :=
    priorMeasure_uniform dp rfl hcardR
  -- Fold the uniform-measure occurrences in the goal to `dp.priorMeasure`.
  rw [show ((Fintype.card W : ℝ≥0∞))⁻¹ • (Measure.count : Measure W)
        = dp.priorMeasure from hdp_priorMeasure.symm]
  have hpm_pt : ∀ w, dp.priorMeasure {w} = ENNReal.ofReal ((Fintype.card W : ℝ))⁻¹ :=
    fun w => priorMeasure_singleton dp w
  have hutil_dp : ∀ w o', dp.utility w o' = -(ℓ w o').toReal := fun _ _ => rfl
  have hprior_dp_val : ∀ w, dp.prior w = ((Fintype.card W : ℝ))⁻¹ := fun _ => rfl
  -- Apply the utility-loss identity to `f` and `g`.
  rw [bayesRisk_deterministic_toReal_utility ℓ hℓ_fin dp hprior_dp_val hdp_prior
        hutil_dp hpm_pt hcardR f,
    bayesRisk_deterministic_toReal_utility ℓ hℓ_fin dp hprior_dp_val hdp_prior
        hutil_dp hpm_pt hcardR g]
  -- Convert questionUtility inequality from h to the sum inequality.
  have hqu := h dp hdp_prior hdp_sum
  rw [questionUtility_image_fibers_eq dp g hdp_prior hdp_sum,
    questionUtility_image_fibers_eq dp f hdp_prior hdp_sum] at hqu
  -- Strip ofReal (RHS nonneg because condValue ≤ 0 when utility ≤ 0).
  have hval_nonneg : ∀ (cm : Finset W), dp.condValue Finset.univ cm ≤ 0 := fun cm => by
    rw [condValue_of_nonempty Finset.univ_nonempty]
    refine Finset.sup'_le _ _ fun o' _ => ?_
    by_cases h0 : cm.sum dp.prior = 0
    · exact (condExpectedUtility_of_eq_zero h0 o').le
    · rw [condExpectedUtility_of_ne_zero h0]
      refine Finset.sum_nonpos fun w _ => ?_
      have hp : 0 ≤ dp.prior w / cm.sum dp.prior :=
        div_nonneg (hdp_prior w)
          (lt_of_le_of_ne (Finset.sum_nonneg fun w _ => hdp_prior w) (Ne.symm h0)).le
      show dp.prior w / cm.sum dp.prior * dp.utility w o' ≤ 0
      show dp.prior w / cm.sum dp.prior * (-(ℓ w o').toReal) ≤ 0
      have := mul_nonneg hp (ENNReal.toReal_nonneg (a := ℓ w o'))
      linarith
  have hcp_nn : ∀ cm : Finset W, 0 ≤ dp.cellProbability cm := fun cm =>
    Finset.sum_nonneg fun w _ => hdp_prior w
  have hRHS_nn : 0 ≤ - ∑ o' : O', dp.cellProbability
        (Finset.univ.filter (g · = o'))
      * dp.condValue Finset.univ (Finset.univ.filter (g · = o')) := by
    rw [neg_nonneg]
    refine Finset.sum_nonpos fun o' _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (hcp_nn _) (hval_nonneg _)
  rw [ENNReal.ofReal_le_ofReal_iff hRHS_nn]
  linarith

end Core.DecisionTheory.DecisionProblem
