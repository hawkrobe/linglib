import Linglib.Core.Constraint.Dequantization.LogSumExp.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Maslov Dequantization: `lse α → max` as `α → ∞`
@cite{litvinov-2005} @cite{maslov-1992}

The defining limit of the warped (log-sum-exp) semiring: as the
inverse temperature `α → ∞`, log-sum-exp deforms to max-plus.

```
  lse α a b  =  (1/α) · log(exp(α·a) + exp(α·b))  ──α → ∞──→  max a b
```

This is **Maslov dequantization** (@cite{litvinov-2005}): a one-parameter
family of commutative semirings on ℝ — the Maslov / "warped" semirings —
that deforms continuously to the max-plus (tropical) semiring as the
temperature parameter sweeps to its limit. The name "dequantization"
emphasises the analogy with the classical limit of quantum mechanics:
the smooth, fluctuation-tolerant semiring becomes a sharp, "winner takes
all" semiring.

For us, the linguistic content is the bridge from MaxEnt (soft / gradient)
constraint frameworks to HG (deterministic / gradient) — and, composed
with the existing exponential-separation bridge V → T from
`ViolationSemiring.lean`, the bridge from MaxEnt all the way to OT
(deterministic / categorical). See `Constraint/Deformation.lean` for the
linguistic-theoretic packaging.

## Proof outline

WLOG `b ≤ a`. The factorization

```
  lse α a b  =  a + (1/α) · log(1 + exp(α · (b - a)))
```

isolates the "winner score" `a` from a non-negative correction term. The
correction is bounded between `0` (when `b ≪ a`, the loser contributes
nothing) and `(log 2) / α` (when `b = a`, the loser contributes a tied
share). Both bounds tend to `0` as `α → ∞`, so the correction tends to
`0` by the squeeze theorem, and `lse α a b → a = max a b`.
-/

namespace Core.Constraint

open Real Filter Topology

-- ============================================================================
-- § 1: Factorization
-- ============================================================================

/-- **Factorization of `lse`.** Extracting `exp(α·a)` from the partition
    function gives

    ```
      lse α a b  =  a  +  (1/α) · log(1 + exp(α · (b - a)))
    ```

    Holds for arbitrary `a, b` (the identity is pure algebra), but is most
    useful when `b ≤ a`: then `a = max a b` and the second term is a
    non-negative "correction" that vanishes as `α → ∞`. -/
theorem lse_eq_max_plus_correction (α : ℝ) (hα : 0 < α) (a b : ℝ) :
    lse α a b = a + (1/α) * log (1 + exp (α * (b - a))) := by
  unfold lse
  have key : exp (α*a) + exp (α*b) = exp (α*a) * (1 + exp (α*(b - a))) := by
    rw [mul_add, mul_one, ← exp_add]
    congr 2
    ring
  have hpos : (0 : ℝ) < 1 + exp (α*(b - a)) := by positivity
  rw [key, Real.log_mul (exp_pos _).ne' hpos.ne', Real.log_exp]
  field_simp

-- ============================================================================
-- § 2: Bounds on the correction term
-- ============================================================================

/-- The correction term `(1/α) · log(1 + exp(α · (b - a)))` is non-negative
    for `α > 0`. -/
theorem correction_nonneg (α : ℝ) (hα : 0 < α) (a b : ℝ) :
    0 ≤ (1/α) * log (1 + exp (α * (b - a))) := by
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  have : 0 ≤ exp (α * (b - a)) := (exp_pos _).le
  linarith

/-- The correction term is bounded above by `(log 2) / α` when `b ≤ a` and
    `α > 0`. (At `b = a` the loser contributes a tied share `log 2`.) -/
theorem correction_le_log2_div (α : ℝ) (hα : 0 < α) (a b : ℝ) (hab : b ≤ a) :
    (1/α) * log (1 + exp (α * (b - a))) ≤ log 2 / α := by
  have hexp_le_one : exp (α * (b - a)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hα.le (by linarith)
  have hlog_le : log (1 + exp (α * (b - a))) ≤ log 2 := by
    apply Real.log_le_log (by linarith [exp_pos (α * (b - a))])
    linarith
  rw [show log 2 / α = (1/α) * log 2 by ring]
  exact mul_le_mul_of_nonneg_left hlog_le (by positivity)

-- ============================================================================
-- § 3: The correction tends to zero
-- ============================================================================

/-- The correction term tends to `0` as `α → ∞`.

    Proof: for `α > 0`, the correction is sandwiched in `[0, (log 2)/α]`
    by `correction_nonneg` and `correction_le_log2_div`; both bounds
    tend to `0` (the upper bound by `tendsto_inv_atTop_zero` scaled by
    the constant `log 2`). -/
theorem correction_tendsto_zero (a b : ℝ) (hab : b ≤ a) :
    Tendsto (fun α => (1/α) * log (1 + exp (α * (b - a)))) atTop (𝓝 0) := by
  have h_log_div : Tendsto (fun α : ℝ => log 2 / α) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    have hzero : (0 : ℝ) = log 2 * 0 := by ring
    rw [hzero]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => (0 : ℝ))
    (h := fun α => log 2 / α) tendsto_const_nhds h_log_div
  · -- 0 ≤ correction, eventually
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    exact correction_nonneg α hα a b
  · -- correction ≤ log 2 / α, eventually
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    exact correction_le_log2_div α hα a b hab

-- ============================================================================
-- § 4: Main theorem — `lse α a b → max a b`
-- ============================================================================

/-- **Maslov dequantization (binary case).** As `α → ∞`,
    `lse α a b → max a b`.

    Equivalently: the warped semiring `(ℝ, lse α, +)` deforms to the
    max-plus (tropical) semiring `(ℝ, max, +)` as `α → ∞`. -/
theorem lse_tendsto_max (a b : ℝ) :
    Tendsto (fun α => lse α a b) atTop (𝓝 (max a b)) := by
  by_cases h : b ≤ a
  · -- Case b ≤ a: max a b = a; use the factorization.
    rw [max_eq_left h]
    have hcorr : Tendsto (fun α : ℝ => a + (1/α) * log (1 + exp (α * (b - a))))
                          atTop (𝓝 (a + 0)) :=
      (correction_tendsto_zero a b h).const_add a
    rw [add_zero] at hcorr
    apply hcorr.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    exact (lse_eq_max_plus_correction α hα a b).symm
  · -- Case a < b: swap via lse_comm; use the factorization on (b, a).
    have hba : a < b := not_le.mp h
    rw [max_eq_right hba.le]
    have hcorr : Tendsto (fun α : ℝ => b + (1/α) * log (1 + exp (α * (a - b))))
                          atTop (𝓝 (b + 0)) :=
      (correction_tendsto_zero b a hba.le).const_add b
    rw [add_zero] at hcorr
    apply hcorr.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    rw [lse_comm]
    exact (lse_eq_max_plus_correction α hα b a).symm

-- ============================================================================
-- § 5: n-ary limit — `lseFinset α cands score → cands.sup' score`
-- ============================================================================

/-! The Finset analogue of `lse_tendsto_max`. The strategy is the same
sandwich, generalised to n candidates: the partition function is bounded
above by `card · exp(α · max)` and below by `exp(α · max)`, so
`lseFinset α cands score` lies in `[max, max + log(card)/α]`, both bounds
collapsing to `max` as `α → ∞`. -/

/-- Lower bound: `cands.sup' hne score ≤ lseFinset α cands score` for `α > 0`.

    The maximum score is achieved at some `c_max ∈ cands` (since `cands`
    is non-empty), so `exp(α · max) ≤ Σ exp(α · score c')`, and taking
    `(1/α) · log` of both sides preserves the inequality (`α > 0`). -/
theorem sup'_le_lseFinset {Cand : Type*} {cands : Finset Cand} (hne : cands.Nonempty)
    (α : ℝ) (hα : 0 < α) (score : Cand → ℝ) :
    cands.sup' hne score ≤ lseFinset α cands score := by
  obtain ⟨c_max, hc_max, hsup_eq⟩ := Finset.exists_mem_eq_sup' hne score
  unfold lseFinset
  rw [hsup_eq, show score c_max = (1/α) * (α * score c_max) by field_simp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show α * score c_max = log (exp (α * score c_max)) from (Real.log_exp _).symm]
  apply Real.log_le_log (Real.exp_pos _)
  exact Finset.single_le_sum (f := fun c' => exp (α * score c'))
    (fun _ _ => (Real.exp_pos _).le) hc_max

/-- Upper bound: `lseFinset α cands score ≤ cands.sup' hne score + log(card)/α`
    for `α > 0`.

    Each summand `exp(α · score c') ≤ exp(α · max)` (since `score c' ≤ max`
    and `α ≥ 0`), so `Σ exp(α · score c') ≤ card · exp(α · max)`. Take
    `(1/α) · log` and split the log of a product. -/
theorem lseFinset_le_sup'_add {Cand : Type*} {cands : Finset Cand}
    (hne : cands.Nonempty) (α : ℝ) (hα : 0 < α) (score : Cand → ℝ) :
    lseFinset α cands score ≤ cands.sup' hne score + log (cands.card) / α := by
  set M := cands.sup' hne score with hM
  have hcard_pos : (0 : ℝ) < cands.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hsum_le : ∑ c' ∈ cands, exp (α * score c') ≤ cands.card * exp (α * M) := by
    calc ∑ c' ∈ cands, exp (α * score c')
        ≤ ∑ _c' ∈ cands, exp (α * M) := by
          apply Finset.sum_le_sum
          intro c' hc'
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (Finset.le_sup' (f := score) hc') hα.le)
      _ = cands.card * exp (α * M) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsum_pos : (0 : ℝ) < ∑ c' ∈ cands, exp (α * score c') :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
  have hprod_pos : (0 : ℝ) < cands.card * exp (α * M) :=
    mul_pos hcard_pos (Real.exp_pos _)
  unfold lseFinset
  calc (1/α) * log (∑ c' ∈ cands, exp (α * score c'))
      ≤ (1/α) * log (cands.card * exp (α * M)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.log_le_log hsum_pos hsum_le
    _ = (1/α) * (log cands.card + α * M) := by
        rw [Real.log_mul hcard_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    _ = M + log cands.card / α := by field_simp; ring

/-- **Maslov dequantization (n-ary case).** As `α → ∞`,
    `lseFinset α cands score → cands.sup' hne score`.

    Sandwich proof: by `sup'_le_lseFinset` and `lseFinset_le_sup'_add`,
    the value lies in `[sup', sup' + log(card)/α]` for `α > 0`; both
    bounds tend to `sup'` because `log(card)/α → 0`. -/
theorem lseFinset_tendsto_sup' {Cand : Type*} {cands : Finset Cand}
    (hne : cands.Nonempty) (score : Cand → ℝ) :
    Tendsto (fun α : ℝ => lseFinset α cands score) atTop
      (𝓝 (cands.sup' hne score)) := by
  set M := cands.sup' hne score with hM
  -- Upper bound function tends to M.
  have h_log_div : Tendsto (fun α : ℝ => log (cands.card : ℝ) / α) atTop (𝓝 0) := by
    simp only [div_eq_mul_inv]
    have hzero : (0 : ℝ) = log cands.card * 0 := by ring
    rw [hzero]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_zero
  have h_upper : Tendsto (fun α : ℝ => M + log (cands.card : ℝ) / α) atTop (𝓝 M) := by
    have := h_log_div.const_add M
    rwa [add_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => M)
    (h := fun α => M + log (cands.card : ℝ) / α) tendsto_const_nhds h_upper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    exact sup'_le_lseFinset hne α hα score
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    exact lseFinset_le_sup'_add hne α hα score

end Core.Constraint
