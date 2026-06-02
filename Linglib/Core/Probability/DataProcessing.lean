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
    simp [Finset.not_nonempty_iff_eq_empty.mp hs, klFun, Real.log_one]

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
any noisy channel can only destroy information about the source.

Hypotheses: `p ≪ q` (otherwise both sides may be `∞` and the inequality
is vacuous in a less interesting way) and `q a ≠ 0 → κ a b ≠ 0` for all
`a, b` where the inequality at `b` matters (encoded via the
`(q.bind κ) b ≠ 0 → ...` flow). For finite-support discrete measures,
both hypotheses reduce to checking at finitely many `(a, b)` pairs.

This is the core principle that drives:
- the cancellation theorem in [goodman-stuhlmuller-2013]
  (less informative speaker access → smaller KL of L1 from prior),
- post-processing of any kernel-decomposed RSA model. -/
theorem klDiv_bind_le [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (p q : PMF α) (κ : α → PMF β)
    (h_ac : MeasureTheory.Measure.AbsolutelyContinuous p.toMeasure q.toMeasure)
    (h_bind_ac : MeasureTheory.Measure.AbsolutelyContinuous
                  (p.bind κ).toMeasure (q.bind κ).toMeasure)
    (h_q_pos : ∀ a, q a ≠ 0)
    (h_κ_pos : ∀ a b, q a ≠ 0 → (q.bind κ) b ≠ 0 → κ a b ≠ 0) :
    (p.bind κ).klDiv (q.bind κ) ≤ p.klDiv q := by
  -- Convert both KL divergences to discrete sums via `klDiv_eq_sum_klFun`.
  rw [klDiv_eq_sum_klFun (p.bind κ) (q.bind κ) h_bind_ac,
      klDiv_eq_sum_klFun p q h_ac]
  -- Standing facts that get used throughout
  have hp_ne_top : ∀ a, p a ≠ ∞ := PMF.apply_ne_top p
  have hq_ne_top : ∀ a, q a ≠ ∞ := PMF.apply_ne_top q
  have hκ_ne_top : ∀ a b, κ a b ≠ ∞ := fun a b => PMF.apply_ne_top (κ a) b
  have hbq_ne_top : ∀ b, (q.bind κ) b ≠ ∞ := PMF.apply_ne_top (q.bind κ)
  have hbp_ne_top : ∀ b, (p.bind κ) b ≠ ∞ := PMF.apply_ne_top (p.bind κ)
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
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact ENNReal.toReal_mul
  have h_bind_toReal_p : ∀ b,
      ((p.bind κ) b).toReal = ∑ a, (p a).toReal * (κ a b).toReal := by
    intro b
    rw [bind_apply_eq_finset_sum,
        ENNReal.toReal_sum (fun a _ =>
          ENNReal.mul_ne_top (hp_ne_top a) (hκ_ne_top a b))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact ENNReal.toReal_mul
  -- κ a is a PMF: ∑_b κ a b = 1 (in ENNReal)
  have h_κ_sum_one : ∀ a, ∑ b, κ a b = 1 := fun a =>
    (PMF.tsum_coe (κ a) ▸ tsum_eq_sum (fun b (h : b ∉ Finset.univ) =>
      absurd (Finset.mem_univ b) h)).symm
  -- The classical klFun_nonneg, used in lifts to ENNReal
  have h_klFun_nn : ∀ x, 0 ≤ x → 0 ≤ _root_.InformationTheory.klFun x :=
    fun _ hx => _root_.InformationTheory.klFun_nonneg hx
  -- Strategy:
  --   Step 1. Rewrite RHS sum: each term q a * ofReal(klFun((p a / q a).toReal))
  --           equals ∑_b (q a * κ a b) * ofReal(klFun((p a / q a).toReal))
  --           via `1 = ∑_b κ a b` lifted into ENNReal.
  --   Step 2. Swap ∑_a ∑_b → ∑_b ∑_a.
  --   Step 3. Per-b inequality: split on `(q.bind κ) b = 0` vs `≠ 0`.
  --           If = 0: both sides zero (each q a * κ a b = 0).
  --           Else:   apply log-sum on ℝ side with weights y_a = (q a * κ a b).toReal,
  --                   points x_a = (p a * κ a b).toReal. Then lift via ofReal.
  -- ============================================================================
  -- Step 1: expand q a = q a * (∑_b κ a b) on RHS, then push sum inside.
  -- ============================================================================
  have h_RHS_expand : (∑ a, q a * ENNReal.ofReal
        (_root_.InformationTheory.klFun ((p a / q a).toReal)))
      = ∑ a, ∑ b, (q a * κ a b) * ENNReal.ofReal
        (_root_.InformationTheory.klFun ((p a / q a).toReal)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    -- Distribute: ∑_b (q a * κ a b) * X = (∑_b q a * κ a b) * X = (q a * ∑_b κ a b) * X = q a * X.
    rw [show (∑ b, (q a * κ a b) * ENNReal.ofReal
              (_root_.InformationTheory.klFun ((p a / q a).toReal)))
          = (∑ b, q a * κ a b) * ENNReal.ofReal
              (_root_.InformationTheory.klFun ((p a / q a).toReal)) from
            (Finset.sum_mul (s := Finset.univ) ..).symm,
        ← Finset.mul_sum, h_κ_sum_one a, mul_one]
  rw [h_RHS_expand, Finset.sum_comm]
  -- ============================================================================
  -- Step 2: pointwise per b.
  -- ============================================================================
  refine Finset.sum_le_sum (fun b _ => ?_)
  -- Per-b goal:
  --   (q.bind κ) b * ofReal(klFun (((p.bind κ) b / (q.bind κ) b).toReal))
  --     ≤ ∑ a, (q a * κ a b) * ofReal(klFun ((p a / q a).toReal))
  by_cases hbq_zero : (q.bind κ) b = 0
  · -- LHS = 0, and each q a * κ a b = 0 in the RHS (since their sum vanishes).
    rw [hbq_zero, zero_mul]
    -- Show RHS ≥ 0 (trivially from non-negativity).
    exact zero_le
  · -- (q.bind κ) b ≠ 0. By h_κ_pos and h_q_pos, κ a b ≠ 0 for all a.
    have h_κ_ne : ∀ a, κ a b ≠ 0 := fun a =>
      h_κ_pos a b (h_q_pos a) hbq_zero
    -- Hence q a * κ a b ≠ 0 (q a ≠ 0 by h_q_pos).
    have hq_κ_ne : ∀ a, q a * κ a b ≠ 0 := fun a =>
      mul_ne_zero (h_q_pos a) (h_κ_ne a)
    -- Strict positivity in ℝ:
    have hqκ_real_pos : ∀ a, 0 < (q a).toReal * (κ a b).toReal := by
      intro a
      refine mul_pos ?_ ?_
      · refine ENNReal.toReal_pos (h_q_pos a) (hq_ne_top a)
      · refine ENNReal.toReal_pos (h_κ_ne a) (hκ_ne_top a b)
    -- (p a / q a).toReal = (p a).toReal / (q a).toReal under hyps.
    have h_pdivq_toReal : ∀ a, ((p a) / (q a)).toReal = (p a).toReal / (q a).toReal :=
      fun a => ENNReal.toReal_div _ _
    -- ((p.bind κ) b / (q.bind κ) b).toReal = (p.bind κ b).toReal / (q.bind κ b).toReal
    have h_bdivb_toReal :
        (((p.bind κ) b) / ((q.bind κ) b)).toReal
          = ((p.bind κ) b).toReal / ((q.bind κ) b).toReal :=
      ENNReal.toReal_div _ _
    -- Total weight Y in ℝ:
    have hY_eq : ((q.bind κ) b).toReal = ∑ a, (q a).toReal * (κ a b).toReal :=
      h_bind_toReal_q b
    have hX_eq : ((p.bind κ) b).toReal = ∑ a, (p a).toReal * (κ a b).toReal :=
      h_bind_toReal_p b
    -- Apply log-sum inequality on ℝ.
    have h_logsum := Real.klFun_logSum_le (Finset.univ : Finset α)
        (fun a => (p a).toReal * (κ a b).toReal)
        (fun a => (q a).toReal * (κ a b).toReal)
        (fun a _ => mul_nonneg (hp_nn a) (hκ_nn a b))
        (fun a _ => hqκ_real_pos a)
    -- Rewrite ∑_a x_a / ∑_a y_a in the log-sum into ((p.bind κ) b / (q.bind κ) b).toReal.
    rw [← hX_eq, ← hY_eq] at h_logsum
    -- Per-a: y_a * klFun(x_a / y_a) = (q a * κ a b).toReal * klFun((p a / q a).toReal).
    -- The κ a b's cancel inside klFun's argument.
    have h_per_a : ∀ a,
        ((q a).toReal * (κ a b).toReal) *
          _root_.InformationTheory.klFun
            (((p a).toReal * (κ a b).toReal) / ((q a).toReal * (κ a b).toReal))
        = ((q a).toReal * (κ a b).toReal) *
          _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal) := by
      intro a
      have hκ_real_ne : (κ a b).toReal ≠ 0 :=
        ne_of_gt (ENNReal.toReal_pos (h_κ_ne a) (hκ_ne_top a b))
      have hq_real_ne : (q a).toReal ≠ 0 :=
        ne_of_gt (ENNReal.toReal_pos (h_q_pos a) (hq_ne_top a))
      have h_div_eq :
          ((p a).toReal * (κ a b).toReal) / ((q a).toReal * (κ a b).toReal)
            = (p a).toReal / (q a).toReal := by
        field_simp
      rw [h_div_eq]
    -- Bridge: the ℝ-side log-sum bound.
    have h_real_bound :
        ((q.bind κ) b).toReal *
          _root_.InformationTheory.klFun
            ((((p.bind κ) b) / ((q.bind κ) b)).toReal)
        ≤ ∑ a, ((q a).toReal * (κ a b).toReal) *
            _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal) := by
      rw [h_bdivb_toReal]
      calc ((q.bind κ) b).toReal *
              _root_.InformationTheory.klFun
                (((p.bind κ) b).toReal / ((q.bind κ) b).toReal)
          ≤ _ := h_logsum
        _ = _ := by simp_rw [h_per_a]
    -- Step 3a: lift the ℝ-side bound to ENNReal via ofReal.
    -- LHS to lift:
    --   (q.bind κ b) * ofReal(klFun (((p.bind κ) b / (q.bind κ) b).toReal))
    --   = ofReal((q.bind κ b).toReal * klFun(...))
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
    -- RHS to lift:
    --   ∑_a (q a * κ a b) * ofReal(klFun((p a / q a).toReal))
    --   = ofReal(∑_a (q a * κ a b).toReal * klFun((p a / q a).toReal))
    have h_summand_RHS : ∀ a, (q a * κ a b) * ENNReal.ofReal
        (_root_.InformationTheory.klFun ((p a / q a).toReal))
        = ENNReal.ofReal ((q a).toReal * (κ a b).toReal *
            _root_.InformationTheory.klFun ((p a).toReal / (q a).toReal)) := by
      intro a
      have h1 : q a * κ a b = ENNReal.ofReal ((q a).toReal * (κ a b).toReal) := by
        rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal
              (ENNReal.mul_ne_top (hq_ne_top a) (hκ_ne_top a b))]
      rw [h_pdivq_toReal a, h1,
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
    refine ENNReal.ofReal_le_ofReal h_real_bound

end PMF
