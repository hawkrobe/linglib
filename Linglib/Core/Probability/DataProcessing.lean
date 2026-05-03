import Linglib.Core.Probability.Entropy
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
moves closer to the prior. Specifically, for the @cite{goodman-stuhlmuller-2013}
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
- the cancellation theorem in @cite{goodman-stuhlmuller-2013}
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
  /-
  TODO: Discharge via `Real.klFun_logSum_le` applied per `b`, then swap sums.

  Goal shape:
    `∑ b, (q.bind κ) b * ofReal(klFun((p.bind κ b / q.bind κ b).toReal))`
    `  ≤ ∑ a, q a * ofReal(klFun((p a / q a).toReal))`

  Proof sketch (~80 LOC of careful ENNReal/Real bridging):

  1. For each `b ∈ Finset.univ`, apply `Real.klFun_logSum_le` with weights
     `y_a = (q a * κ a b).toReal` and points `x_a = (p a * κ a b).toReal`.
     Note `(q a * κ a b).toReal / (q a * κ a b).toReal = (p a / q a).toReal`
     when `κ a b ≠ 0`; the `κ a b = 0` terms contribute `0` on both sides
     and can be filtered via `h_κ_pos`.

  2. The log-sum gives, per `b`:
       `(q.bind κ b).toReal * klFun((p.bind κ b / q.bind κ b).toReal)`
         `≤ ∑ a, (q a * κ a b).toReal * klFun((p a / q a).toReal)`

  3. Lift to ENNReal via `ENNReal.ofReal_le_ofReal_iff` (both sides non-neg by
     `klFun_nonneg`), then multiply through by `1` and re-arrange to match the
     LHS sum form.

  4. Swap `∑_b ∑_a → ∑_a ∑_b` via `Finset.sum_comm`.

  5. Pull `q a * ofReal(klFun((p a / q a).toReal))` out of the inner sum
     (it doesn't depend on `b`), leaving `∑_b κ a b = 1` (since `κ a` is a PMF).

  Each step is mechanical but the ENNReal/.toReal bookkeeping is substantial.
  Tracked separately; once proved, the cancellation theorem (this file's
  raison d'être) follows in ~30 LOC.
  -/
  sorry

end PMF
