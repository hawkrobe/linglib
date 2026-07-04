import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Certified atoms for transcendental RSA models

RSA models with real-exponent utilities or exponential costs reduce, after
exact-rational bookkeeping, to a handful of named transcendental *atoms*:
n-th roots of explicit rationals (softmax utilities with denominator-`n`
weights) and `exp` of negated rational costs. This file provides the atoms
and their two-sided rational-bound certificates, so study-level predictions
close by `nlinarith` over kernel-checked power inequalities.

* `rootAtom X n` is `X ^ (n⁻¹ : ℝ)`: bound it by exhibiting `r ^ n ≤ X` and
  `X ≤ s ^ n`, both kernel-checkable when `r`, `s`, `X` are rational.
* `expAtom q` is `exp (−q)`: for rational `q = m / n` the identity
  `expAtom q ^ n * exp m = 1` turns digit bounds on `e` into two-sided
  bounds on the atom.

## Main results

* `le_rootAtom_of_pow_le`, `rootAtom_le_of_le_pow`, `rootAtom_mem_Icc` —
  n-th-root certificates.
* `rootAtom_eq_exp` — the bridge to the paper-facing `exp`/`log` form.
* `expAtom_pow_mul_exp_eq_one` — the inversion identity for cost atoms.
-/

open Real

namespace RSA

/-! ### Root atoms -/

/-- The `n`-th root of `X` as a real power. For rational `X` this is the
shape of softmax utilities with denominator-`n` weights. -/
noncomputable def rootAtom (X : ℝ) (n : ℕ) : ℝ := X ^ ((n : ℝ)⁻¹)

theorem rootAtom_pos {X : ℝ} (hX : 0 < X) (n : ℕ) : 0 < rootAtom X n :=
  Real.rpow_pos_of_pos hX _

/-- Lower certificate: `r ^ n ≤ X` gives `r ≤ ⁿ√X`
(mathlib's `Real.le_rpow_inv_iff_of_pos` at a natural exponent). -/
theorem le_rootAtom_of_pow_le {r X : ℝ} {n : ℕ} (hn : n ≠ 0) (hr : 0 ≤ r)
    (h : r ^ n ≤ X) : r ≤ rootAtom X n :=
  (Real.le_rpow_inv_iff_of_pos hr (le_trans (by positivity) h)
    (by exact_mod_cast hn.bot_lt)).mpr (by rwa [Real.rpow_natCast])

/-- Upper certificate: `X ≤ s ^ n` gives `ⁿ√X ≤ s`
(mathlib's `Real.rpow_inv_le_iff_of_pos` at a natural exponent). -/
theorem rootAtom_le_of_le_pow {X s : ℝ} {n : ℕ} (hn : n ≠ 0) (hX : 0 ≤ X)
    (hs : 0 ≤ s) (h : X ≤ s ^ n) : rootAtom X n ≤ s :=
  (Real.rpow_inv_le_iff_of_pos hX hs
    (by exact_mod_cast hn.bot_lt)).mpr (by rwa [Real.rpow_natCast])

/-- Two-sided certificate from kernel-checkable power bounds. -/
theorem rootAtom_mem_Icc {r X s : ℝ} {n : ℕ} (hn : n ≠ 0) (hr : 0 ≤ r)
    (hX : 0 ≤ X) (hs : 0 ≤ s) (hlo : r ^ n ≤ X) (hhi : X ≤ s ^ n) :
    rootAtom X n ∈ Set.Icc r s :=
  ⟨le_rootAtom_of_pow_le hn hr hlo, rootAtom_le_of_le_pow hn hX hs hhi⟩

/-- Bridge to the paper-facing exponential form:
`ⁿ√X = exp (log X / n)` for positive `X`. (The `log X * n⁻¹` orientation
is what `rpow_def_of_pos` produces; commute afterwards as needed.) -/
theorem rootAtom_eq_exp {X : ℝ} (hX : 0 < X) (n : ℕ) :
    rootAtom X n = Real.exp (Real.log X / n) := by
  rw [rootAtom, Real.rpow_def_of_pos hX, div_eq_mul_inv]

/-- The two-factor exponential form: the n-th root of `a^j · b^k` is the
weighted geometric mean `exp ((j/n)·log a + (k/n)·log b)` — the shape of
softmax utilities with denominator-`n` noise weights. -/
theorem rootAtom_pow_mul_pow {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (j k n : ℕ) :
    rootAtom (a ^ j * b ^ k) n =
      Real.exp ((j / n : ℝ) * Real.log a + (k / n : ℝ) * Real.log b) := by
  rw [rootAtom, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast a j, ← Real.rpow_natCast b k,
    ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le,
    Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
  congr 1
  ring

/-! ### Two-factor geometric means

`b ^ w * a ^ (1 − w)` is the channel-weighted geometric mean of two
literal posteriors — eq.-7-style speaker utilities for a binary-support
noise channel. The strict bounds against a comparison value need no
magnitude computation: a weighted GM sits strictly between its factors. -/

/-- A two-factor GM is strictly below `c` when one factor is at most `c`
and the other strictly below, its weight positive. -/
theorem rpow_mul_rpow_lt {a b c w w' : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hb : 0 < b) (hbc : b ≤ c) (hac : a < c) (hw : 0 ≤ w) (hw' : 0 < w')
    (hsum : w + w' = 1) : b ^ w * a ^ w' < c := by
  calc b ^ w * a ^ w'
      ≤ c ^ w * a ^ w' := by gcongr
    _ < c ^ w * c ^ w' :=
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha.le hac hw') (by positivity)
    _ = c := by rw [← Real.rpow_add hc, hsum, Real.rpow_one]

/-- A two-factor GM is strictly above `c` when one factor is at least `c`
and the other strictly above, its weight positive. -/
theorem lt_rpow_mul_rpow {a b c w w' : ℝ} (hc : 0 < c) (ha : c < a)
    (hcb : c ≤ b) (hw : 0 ≤ w) (hw' : 0 < w') (hsum : w + w' = 1) :
    c < b ^ w * a ^ w' := by
  calc c = c ^ w * c ^ w' := by rw [← Real.rpow_add hc, hsum, Real.rpow_one]
    _ < c ^ w * a ^ w' :=
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hc.le ha hw') (by positivity)
    _ ≤ b ^ w * a ^ w' :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hc.le hcb hw)
          (Real.rpow_nonneg (hc.trans ha).le _)

/-! ### Exponential cost atoms -/

/-- The multiplicative cost factor `exp (−q)` for a cost `q`. -/
noncomputable def expAtom (q : ℝ) : ℝ := Real.exp (-q)

theorem expAtom_pos (q : ℝ) : 0 < expAtom q := Real.exp_pos _

/-- The inversion identity: for `q = m / n`, `expAtom q ^ n · exp m = 1`.
Combined with digit bounds on `exp m` (from `Real.exp_one_gt_d9` /
`exp_one_lt_d9` raised by `pow_lt_pow_left₀`), this yields two-sided
rational bounds on the atom via kernel-checked power comparisons. -/
theorem expAtom_pow_mul_exp_eq_one {m : ℝ} {n : ℕ} (hn : n ≠ 0) :
    expAtom (m / n) ^ n * Real.exp m = 1 := by
  rw [expAtom, ← Real.exp_nat_mul,
    show (n : ℝ) * -(m / n) = -m by
      field_simp,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero]

end RSA
