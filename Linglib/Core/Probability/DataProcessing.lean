import Linglib.Core.Probability.Entropy
import Linglib.Core.Probability.Posterior
import Mathlib.Analysis.Convex.Jensen

/-!
# Data processing inequality for `PMF.klDiv` (finite-case)

The data processing inequality (DPI) states that applying a (Markov) kernel
to two distributions can only decrease their KL divergence:

  `klDiv (p.bind κ) (q.bind κ) ≤ klDiv p q`

This file proves DPI for PMFs over `Fintype`s, plus the underlying log-sum
inequality from which DPI follows.

## Main results

- `Real.klFun_logSum_le`: log-sum inequality —
  `Y * klFun(X / Y) ≤ ∑ b_i * klFun(a_i / b_i)` for non-negative reals.
- `PMF.klDiv_bind_le`: DPI for bind on finite types.
- `PMF.klDiv_map_le`: DPI for map (deterministic kernel) on finite types.

## Application

DPI is the structural foundation for "informativity" claims in RSA-style
models: as an observation kernel becomes noisier, the listener's posterior
moves closer to the prior. Specifically, for the [goodman-stuhlmuller-2013]
cancellation theorem, DPI says that as speaker access decreases (kernel
becomes less informative), `KL(L1(a, u) ‖ prior)` decreases — the
listener gains less information from the utterance.
-/

set_option autoImplicit false

open Finset

namespace Real

open InformationTheory

/-- **Log-sum inequality (klFun version)**: for non-negative reals
`x_i, y_i` with `y_i > 0` summing to `Y` and `x_i` summing to `X`,
`Y * klFun(X / Y) ≤ ∑ y_i * klFun(x_i / y_i)`.

A direct corollary of Jensen's inequality applied to the convex function
`klFun` on `[0, ∞)`, with weights `w_i = y_i / Y`.

This is the foundation for the data processing inequality on KL divergence:
when we marginalize a finite-supported distribution, the KL of marginals is
at most the KL of joints. -/
theorem klFun_logSum_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 < y i) :
    (∑ i ∈ s, y i) * klFun ((∑ i ∈ s, x i) / (∑ i ∈ s, y i)) ≤
      ∑ i ∈ s, y i * klFun (x i / y i) := by
  -- Edge case: empty sum
  by_cases hs : s.Nonempty
  · -- Apply Jensen with weights w_i = y_i / Y
    have hY_pos : 0 < ∑ i ∈ s, y i :=
      Finset.sum_pos hy hs
    have hY_ne : (∑ i ∈ s, y i) ≠ 0 := hY_pos.ne'
    -- Weights
    set w : ι → ℝ := fun i => y i / (∑ i ∈ s, y i) with hw_def
    have hw_nn : ∀ i ∈ s, 0 ≤ w i := fun i hi => by
      simp [w, div_nonneg (hy i hi).le hY_pos.le]
    have hw_sum : ∑ i ∈ s, w i = 1 := by
      simp [w, ← Finset.sum_div, div_self hY_ne]
    -- Points: p_i = x_i / y_i
    set p : ι → ℝ := fun i => x i / y i with hp_def
    have hp_mem : ∀ i ∈ s, p i ∈ Set.Ici (0 : ℝ) := fun i hi => by
      simp [p, div_nonneg (hx i hi) (hy i hi).le]
    -- Apply Jensen: klFun (∑ w_i • p_i) ≤ ∑ w_i • klFun (p_i)
    have h_jensen :=
      InformationTheory.convexOn_klFun.map_sum_le hw_nn hw_sum hp_mem
    -- Simplify the inputs
    -- ∑ w_i • p_i = ∑ (y_i / Y) * (x_i / y_i) = (∑ x_i) / Y
    have h_lhs_in : (∑ i ∈ s, w i • p i) = (∑ i ∈ s, x i) / (∑ i ∈ s, y i) := by
      simp only [smul_eq_mul, w, p]
      rw [show (∑ i ∈ s, y i / (∑ j ∈ s, y j) * (x i / y i)) =
            ∑ i ∈ s, x i / (∑ j ∈ s, y j) from by
            apply Finset.sum_congr rfl
            intro i hi
            have hy_ne : y i ≠ 0 := (hy i hi).ne'
            field_simp]
      rw [← Finset.sum_div]
    rw [h_lhs_in] at h_jensen
    -- ∑ w_i • klFun (p_i) = (1/Y) * ∑ y_i * klFun (x_i / y_i)
    have h_rhs_in : (∑ i ∈ s, w i • klFun (p i)) =
        (1 / ∑ i ∈ s, y i) * ∑ i ∈ s, y i * klFun (x i / y i) := by
      simp only [smul_eq_mul, w, p]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_rhs_in] at h_jensen
    -- Multiply both sides by Y > 0
    have := mul_le_mul_of_nonneg_left h_jensen hY_pos.le
    rw [← mul_assoc, mul_one_div, div_self hY_ne, one_mul] at this
    exact this
  · -- Empty s: both sides are 0 (empty sum)
    simp [Finset.not_nonempty_iff_eq_empty.mp hs, klFun]

end Real

namespace PMF

open Finset InformationTheory

open scoped ENNReal

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Data Processing Inequality for `PMF.klDiv` (finite case)**:
applying a Markov kernel `κ : α → PMF β` to two PMFs cannot increase
their KL divergence:
  `klDiv (p.bind κ) (q.bind κ) ≤ klDiv p q`.

The information-theoretic content: post-processing observations through
any noisy channel can only destroy information about the source. The only
hypothesis is absolute continuity `p ≪ q`; absolute continuity of the
binds is derived. -/
theorem klDiv_bind_le [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p q : PMF α) (κ : α → PMF β)
    (h_ac : MeasureTheory.Measure.AbsolutelyContinuous p.toMeasure q.toMeasure) :
    (p.bind κ).klDiv (q.bind κ) ≤ p.klDiv q := by
  classical
  -- Atom-level absolute continuity, and its lift to the binds.
  have h_ac_atom : ∀ a, q a = 0 → p a = 0 := by
    intro a hqa
    have hQ : q.toMeasure {a} = 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]; exact hqa
    have hP := h_ac hQ
    rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)] at hP
  have h_bind_atom : ∀ b, (q.bind κ) b = 0 → (p.bind κ) b = 0 := by
    intro b hqb
    rw [PMF.bind_apply] at hqb ⊢
    rw [ENNReal.tsum_eq_zero] at hqb ⊢
    intro a
    rcases mul_eq_zero.mp (hqb a) with hqa | hκ
    · rw [h_ac_atom a hqa, zero_mul]
    · rw [hκ, mul_zero]
  have h_bind_ac : MeasureTheory.Measure.AbsolutelyContinuous
      (p.bind κ).toMeasure (q.bind κ).toMeasure := by
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
    rw [PMF.toMeasure_apply_eq_zero_iff _ ht] at h0 ⊢
    exact fun u hu hut => Set.disjoint_left.mpr
      (fun b hb hbt => Set.disjoint_left.mp h0
        (PMF.mem_support_iff _ b |>.mpr fun hz =>
          (PMF.mem_support_iff _ b |>.mp hb) (h_bind_atom b hz)) hbt) hu hut
  -- Convert both KL divergences to discrete sums via `klDiv_eq_sum_klFun`.
  rw [klDiv_eq_sum_klFun (p.bind κ) (q.bind κ) h_bind_ac,
      klDiv_eq_sum_klFun p q h_ac]
  -- Standing facts that get used throughout
  have hp_ne_top : ∀ a, p a ≠ ∞ := PMF.apply_ne_top p
  have hq_ne_top : ∀ a, q a ≠ ∞ := PMF.apply_ne_top q
  have hκ_ne_top : ∀ a b, κ a b ≠ ∞ := fun a b => PMF.apply_ne_top (κ a) b
  have hbq_ne_top : ∀ b, (q.bind κ) b ≠ ∞ := PMF.apply_ne_top (q.bind κ)
  have hp_nn : ∀ a, (0 : ℝ) ≤ (p a).toReal := fun _ => ENNReal.toReal_nonneg
  have hq_nn : ∀ a, (0 : ℝ) ≤ (q a).toReal := fun _ => ENNReal.toReal_nonneg
  have hκ_nn : ∀ a b, (0 : ℝ) ≤ (κ a b).toReal := fun _ _ => ENNReal.toReal_nonneg
  -- toReal of the bind: (q.bind κ b).toReal = ∑ a, (q a).toReal * (κ a b).toReal
  have h_bind_toReal_q : ∀ b,
      ((q.bind κ) b).toReal = ∑ a, (q a).toReal * (κ a b).toReal := by
    intro b
    rw [bind_apply_eq_finset_sum,
        ENNReal.toReal_sum (fun a _ =>
          ENNReal.mul_ne_top (hq_ne_top a) (hκ_ne_top a b))]
    exact Finset.sum_congr rfl (fun a _ => ENNReal.toReal_mul)
  have h_bind_toReal_p : ∀ b,
      ((p.bind κ) b).toReal = ∑ a, (p a).toReal * (κ a b).toReal := by
    intro b
    rw [bind_apply_eq_finset_sum,
        ENNReal.toReal_sum (fun a _ =>
          ENNReal.mul_ne_top (hp_ne_top a) (hκ_ne_top a b))]
    exact Finset.sum_congr rfl (fun a _ => ENNReal.toReal_mul)
  -- κ a is a PMF: ∑_b κ a b = 1 (in ENNReal)
  have h_κ_sum_one : ∀ a, ∑ b, κ a b = 1 := fun a =>
    (PMF.tsum_coe (κ a) ▸ tsum_eq_sum (fun b (h : b ∉ Finset.univ) =>
      absurd (Finset.mem_univ b) h)).symm
  have h_klFun_nn : ∀ x, 0 ≤ x → 0 ≤ _root_.InformationTheory.klFun x :=
    fun _ hx => _root_.InformationTheory.klFun_nonneg hx
  -- Step 1: expand q a = q a * (∑_b κ a b) on RHS, then push sum inside.
  have h_RHS_expand : (∑ a, q a * ENNReal.ofReal
        (_root_.InformationTheory.klFun ((p a / q a).toReal)))
      = ∑ a, ∑ b, (q a * κ a b) * ENNReal.ofReal
        (_root_.InformationTheory.klFun ((p a / q a).toReal)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [show (∑ b, (q a * κ a b) * ENNReal.ofReal
              (_root_.InformationTheory.klFun ((p a / q a).toReal)))
          = (∑ b, q a * κ a b) * ENNReal.ofReal
              (_root_.InformationTheory.klFun ((p a / q a).toReal)) from
            (Finset.sum_mul (s := Finset.univ) ..).symm,
        ← Finset.mul_sum, h_κ_sum_one a, mul_one]
  rw [h_RHS_expand, Finset.sum_comm]
  -- Step 2: pointwise per b.
  refine Finset.sum_le_sum (fun b _ => ?_)
  by_cases hbq_zero : (q.bind κ) b = 0
  · rw [hbq_zero, zero_mul]
    exact zero_le
  · -- Restrict the log-sum inequality to the support of `a ↦ q a * κ a b`.
    set t : Finset α := Finset.univ.filter (fun a => q a * κ a b ≠ 0) with ht_def
    have h_mem : ∀ a ∈ t, q a ≠ 0 ∧ κ a b ≠ 0 := fun a ha =>
      mul_ne_zero_iff.mp (Finset.mem_filter.mp ha).2
    have h_notMem : ∀ a ∉ t, q a = 0 ∨ κ a b = 0 := fun a ha =>
      mul_eq_zero.mp (not_not.mp fun hne =>
        ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩))
    -- Off-support, both real summands vanish (using atom-level AC for `p`).
    have h_x_zero : ∀ a ∉ t, (p a).toReal * (κ a b).toReal = 0 := by
      intro a ha
      rcases h_notMem a ha with hqa | hκa
      · rw [h_ac_atom a hqa, ENNReal.toReal_zero, zero_mul]
      · rw [hκa, ENNReal.toReal_zero, mul_zero]
    have h_y_zero : ∀ a ∉ t, (q a).toReal * (κ a b).toReal = 0 := by
      intro a ha
      rcases h_notMem a ha with hqa | hκa
      · rw [hqa, ENNReal.toReal_zero, zero_mul]
      · rw [hκa, ENNReal.toReal_zero, mul_zero]
    have h_x_sum : ∑ a ∈ t, (p a).toReal * (κ a b).toReal
        = ((p.bind κ) b).toReal := by
      rw [h_bind_toReal_p b]
      exact Finset.sum_subset (Finset.subset_univ t)
        (fun a _ ha => h_x_zero a ha)
    have h_y_sum : ∑ a ∈ t, (q a).toReal * (κ a b).toReal
        = ((q.bind κ) b).toReal := by
      rw [h_bind_toReal_q b]
      exact Finset.sum_subset (Finset.subset_univ t)
        (fun a _ ha => h_y_zero a ha)
    -- Log-sum inequality over the support.
    have h_logsum := Real.klFun_logSum_le t
        (fun a => (p a).toReal * (κ a b).toReal)
        (fun a => (q a).toReal * (κ a b).toReal)
        (fun a _ => mul_nonneg (hp_nn a) (hκ_nn a b))
        (fun a ha => mul_pos
          (ENNReal.toReal_pos (h_mem a ha).1 (hq_ne_top a))
          (ENNReal.toReal_pos (h_mem a ha).2 (hκ_ne_top a b)))
    rw [h_x_sum, h_y_sum] at h_logsum
    -- On-support, the κ factors cancel inside `klFun`.
    have h_per_a : ∀ a ∈ t,
        ((q a).toReal * (κ a b).toReal) *
          _root_.InformationTheory.klFun
            (((p a).toReal * (κ a b).toReal) / ((q a).toReal * (κ a b).toReal))
        = ((q a).toReal * (κ a b).toReal) *
          _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal) := by
      intro a ha
      have hκ_real_ne : (κ a b).toReal ≠ 0 :=
        (ENNReal.toReal_pos (h_mem a ha).2 (hκ_ne_top a b)).ne'
      have hq_real_ne : (q a).toReal ≠ 0 :=
        (ENNReal.toReal_pos (h_mem a ha).1 (hq_ne_top a)).ne'
      congr 1
      field_simp
    -- Assemble the ℝ-side bound over the full index set.
    have h_real_bound :
        ((q.bind κ) b).toReal *
          _root_.InformationTheory.klFun
            ((((p.bind κ) b) / ((q.bind κ) b)).toReal)
        ≤ ∑ a, ((q a).toReal * (κ a b).toReal) *
            _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal) := by
      rw [ENNReal.toReal_div]
      calc ((q.bind κ) b).toReal *
              _root_.InformationTheory.klFun
                (((p.bind κ) b).toReal / ((q.bind κ) b).toReal)
          ≤ ∑ a ∈ t, ((q a).toReal * (κ a b).toReal) *
              _root_.InformationTheory.klFun
                (((p a).toReal * (κ a b).toReal)
                  / ((q a).toReal * (κ a b).toReal)) := h_logsum
        _ = ∑ a ∈ t, ((q a).toReal * (κ a b).toReal) *
              _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal) :=
            Finset.sum_congr rfl h_per_a
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ t)
            (fun a _ _ => mul_nonneg (mul_nonneg (hq_nn a) (hκ_nn a b))
              (h_klFun_nn _ (div_nonneg (hp_nn a) (hq_nn a))))
    -- Lift the ℝ-side bound to ENNReal via ofReal.
    have h_LHS_ofReal : ((q.bind κ) b) * ENNReal.ofReal
        (_root_.InformationTheory.klFun
          ((((p.bind κ) b) / ((q.bind κ) b)).toReal))
        = ENNReal.ofReal (((q.bind κ) b).toReal *
            _root_.InformationTheory.klFun
              ((((p.bind κ) b) / ((q.bind κ) b)).toReal)) := by
      rw [show ((q.bind κ) b) * ENNReal.ofReal
              (_root_.InformationTheory.klFun
                ((((p.bind κ) b) / ((q.bind κ) b)).toReal))
            = ENNReal.ofReal ((q.bind κ) b).toReal * ENNReal.ofReal
              (_root_.InformationTheory.klFun
                ((((p.bind κ) b) / ((q.bind κ) b)).toReal)) from by
            congr 1
            exact (ENNReal.ofReal_toReal (hbq_ne_top b)).symm,
          ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    have h_summand_RHS : ∀ a, (q a * κ a b) * ENNReal.ofReal
        (_root_.InformationTheory.klFun ((p a / q a).toReal))
        = ENNReal.ofReal ((q a).toReal * (κ a b).toReal *
            _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal)) := by
      intro a
      have h1 : q a * κ a b = ENNReal.ofReal ((q a).toReal * (κ a b).toReal) := by
        rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal
              (ENNReal.mul_ne_top (hq_ne_top a) (hκ_ne_top a b))]
      rw [ENNReal.toReal_div, h1,
          ← ENNReal.ofReal_mul (mul_nonneg (hq_nn a) (hκ_nn a b))]
    have h_RHS_ofReal :
        (∑ a, (q a * κ a b) * ENNReal.ofReal
            (_root_.InformationTheory.klFun ((p a / q a).toReal)))
          = ENNReal.ofReal (∑ a, ((q a).toReal * (κ a b).toReal *
              _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal))) := by
      simp_rw [h_summand_RHS]
      rw [← ENNReal.ofReal_sum_of_nonneg
            (fun a _ => mul_nonneg (mul_nonneg (hq_nn a) (hκ_nn a b))
              (h_klFun_nn _ (div_nonneg (hp_nn a) (hq_nn a))))]
    rw [h_LHS_ofReal, h_RHS_ofReal]
    exact ENNReal.ofReal_le_ofReal h_real_bound

/-! ### Data processing for mutual information

Garbling one coordinate of a joint distribution through a channel cannot
increase mutual information. This is the form of the DPI that constrains
memory models: a representation generated from a context can carry no more
information about another variable than the context itself
([futrell-gibson-levy-2020] §3.2).
-/

variable {γ : Type*} [Fintype γ]

/-- A joint distribution is absolutely continuous with respect to the product
    of its marginals. -/
theorem toMeasure_absolutelyContinuous_product
    [MeasurableSpace α] [MeasurableSpace β] [DecidableEq α] [DecidableEq β]
    [MeasurableSpace (α × β)] [MeasurableSingletonClass (α × β)]
    (joint : PMF (α × β)) :
    MeasureTheory.Measure.AbsolutelyContinuous joint.toMeasure
      (joint.fst.product joint.snd).toMeasure := by
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun t ht h0 => ?_
  rw [PMF.toMeasure_apply_eq_zero_iff _ ht] at h0 ⊢
  refine Set.disjoint_left.mpr fun x hx hxt =>
    Set.disjoint_left.mp h0 ?_ hxt
  rw [PMF.mem_support_iff] at hx ⊢
  rw [product_apply]
  intro hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hx (le_zero_iff.mp (h ▸ apply_le_fst joint x))
  · exact hx (le_zero_iff.mp (h ▸ apply_le_snd joint x))

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Garbling the second coordinate preserves the first marginal. -/
theorem fst_bind_snd (joint : PMF (α × β)) (κ : β → PMF γ) :
    (joint.bind fun x => (κ x.2).map (Prod.mk x.1)).fst = joint.fst := by
  unfold fst
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  have : ∀ x : α × β, (κ x.2).map (Prod.fst ∘ Prod.mk x.1) = PMF.pure x.1 := by
    intro x
    rw [show Prod.fst ∘ Prod.mk x.1 = Function.const γ x.1 from rfl, PMF.map_const]
  simp only [this]
  exact (PMF.bind_pure_comp _ _)

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Garbling the second coordinate pushes the second marginal through the
    channel. -/
theorem snd_bind_snd (joint : PMF (α × β)) (κ : β → PMF γ) :
    (joint.bind fun x => (κ x.2).map (Prod.mk x.1)).snd = joint.snd.bind κ := by
  unfold snd
  rw [PMF.map_bind, PMF.bind_map]
  simp only [PMF.map_comp]
  have : ∀ x : α × β, (κ x.2).map (Prod.snd ∘ Prod.mk x.1) = κ x.2 := by
    intro x
    rw [show Prod.snd ∘ Prod.mk x.1 = id from rfl, PMF.map_id]
  simp only [this]
  rfl

omit [Fintype α] [Fintype β] [Fintype γ] in
/-- Garbling commutes with forming the product of marginals. -/
theorem product_bind (P : PMF α) (Q : PMF β) (κ : β → PMF γ) :
    (P.product Q).bind (fun x => (κ x.2).map (Prod.mk x.1))
      = P.product (Q.bind κ) := by
  unfold product
  rw [PMF.bind_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.bind_map, PMF.map_bind]
  rfl

/-- **Data processing inequality, mutual-information form**: passing one
    coordinate of a joint distribution through a channel cannot increase
    mutual information. -/
theorem mutualInformation_bind_snd_le
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [DecidableEq α] [DecidableEq β]
    (joint : PMF (α × β)) (κ : β → PMF γ) :
    mutualInformation (joint.bind fun x => (κ x.2).map (Prod.mk x.1))
      ≤ mutualInformation joint := by
  unfold mutualInformation
  refine ENNReal.toReal_mono
    (klDiv_ne_top (toMeasure_absolutelyContinuous_product joint)
      MeasureTheory.Integrable.of_finite) ?_
  rw [fst_bind_snd, snd_bind_snd, ← product_bind]
  exact klDiv_bind_le joint (joint.fst.product joint.snd) _
    (toMeasure_absolutelyContinuous_product joint)

/-! ### Expected Bayes surprisal is conditional entropy

The Bayes-optimal predictor of the first coordinate from the second is the
conditional `G(a,b)/G.snd(b)`; its expected surprisal is the conditional
entropy `H(fst | snd) = H(G) − H(G.snd)`. -/

/-- The expected surprisal of the Bayes-optimal predictor of `fst` from `snd`
    is the conditional entropy `H(G) − H(G.snd)`. -/
theorem sum_mul_neg_log_bayes [DecidableEq β] (G : PMF (α × β)) :
    ∑ x : α × β, (G x).toReal
        * (-Real.log ((G x).toReal / (G.snd x.2).toReal))
      = G.entropy - G.snd.entropy := by
  have key : ∀ x : α × β, (G x).toReal
      * (-Real.log ((G x).toReal / (G.snd x.2).toReal))
      = Real.negMulLog (G x).toReal
        + (G x).toReal * Real.log (G.snd x.2).toReal := by
    intro x
    by_cases hx : (G x).toReal = 0
    · simp [hx, Real.negMulLog]
    · have hGx : G x ≠ 0 := fun h => hx (by rw [h, ENNReal.toReal_zero])
      rw [Real.log_div hx (ENNReal.toReal_ne_zero.mpr
          ⟨snd_apply_ne_zero hGx, PMF.apply_ne_top _ _⟩), Real.negMulLog]
      ring
  simp_rw [key]
  rw [Finset.sum_add_distrib,
    sum_toReal_mul_snd G (fun b => Real.log (G.snd b).toReal),
    show ∑ x : α × β, Real.negMulLog (G x).toReal = G.entropy from rfl,
    entropy_eq_neg_sum_mul_log G.snd]
  ring

end PMF
