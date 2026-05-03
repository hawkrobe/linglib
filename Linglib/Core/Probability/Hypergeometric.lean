import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The hypergeometric PMF

The hypergeometric distribution describes sampling without replacement from
a finite population. Drawing `n` items from a population of `N` containing
`K` successes (and `N - K` failures), the probability of observing exactly
`k` successes is

  `P(k | N, K, n) = C(K, k) · C(N − K, n − k) / C(N, n)`

This file defines `PMF.hypergeometric N K n` as a `PMF (Fin (n + 1))` and
proves the sum-to-1 condition via Chu-Vandermonde's identity
(`Nat.add_choose_eq`).

## Main definitions

- `PMF.hypergeometric N K n h_n h_K`: the PMF for given parameters with
  `n ≤ N` and `K ≤ N`.
- `PMF.hypergeometric_apply`: the closed-form value at each `k`.

## Use cases in linglib

- @cite{goodman-stuhlmuller-2013}: speaker observation of marbles (N = 3).
- @cite{herbstritt-franke-2019}: urn-based probability expressions (N = 10).

Both papers previously open-coded the `C(K, k) · C(N - K, n - k)`
numerator and the `C(N, n)` denominator separately in their `obsKernelRaw`
and `PMF.normalize` machinery. With this primitive, the observation kernel
is a one-line definition.
-/

set_option autoImplicit false

namespace PMF

open ENNReal Finset

/-- **Vandermonde's identity, sum form**: when `K ≤ N`,
`∑ k ∈ range (n + 1), C(K, k) * C(N - K, n - k) = C(N, n)`.

A `Finset.range`-style restatement of `Nat.add_choose_eq`, with the
substitution `m := K`, `n := N - K` (using `K + (N - K) = N` from `K ≤ N`),
and the antidiagonal-to-range conversion. -/
theorem _root_.Nat.sum_choose_mul_choose_eq (N K n : ℕ) (h_K : K ≤ N) :
    (∑ k ∈ range (n + 1), K.choose k * (N - K).choose (n - k)) = N.choose n := by
  conv_rhs => rw [show N = K + (N - K) from (Nat.add_sub_cancel' h_K).symm]
  rw [Nat.add_choose_eq, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (f := fun a b => K.choose a * (N - K).choose b)]

/-- The hypergeometric PMF: probability of observing exactly `k` successes
when drawing `n` items without replacement from a population of `N`
containing `K` successes.

Requires `n ≤ N` and `K ≤ N` (otherwise `C(N, n) = 0` would make the
denominator vanish). The numerator `C(K, k) · C(N - K, n - k)` automatically
returns 0 for impossible combinations (`k > K` or `n - k > N - K`) via the
behavior of `Nat.choose`. -/
noncomputable def hypergeometric (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N) :
    PMF (Fin (n + 1)) :=
  PMF.ofFintype
    (fun k => (K.choose k.val * (N - K).choose (n - k.val) : ℕ) / (N.choose n : ℝ≥0∞))
    (by
      -- Sum-to-1 via Vandermonde: ∑ k, [num k] / denom = (∑ k, num k) / denom
      -- = N.choose n / N.choose n = 1.
      have h_denom_ne_zero : (N.choose n : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos h_n).ne'
      have h_denom_ne_top : (N.choose n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      -- Factor out the denominator: ∑ x/d = (∑ x) * d⁻¹
      simp_rw [ENNReal.div_eq_inv_mul]
      rw [← Finset.mul_sum]
      -- Sum the numerators: ∑ k : Fin (n+1), C(K, k) * C(N-K, n-k) = N.choose n
      rw [show (∑ k : Fin (n + 1),
                 ((K.choose k.val * (N - K).choose (n - k.val) : ℕ) : ℝ≥0∞)) =
               ((N.choose n : ℕ) : ℝ≥0∞) from by
            rw [← Nat.cast_sum, Fin.sum_univ_eq_sum_range
                  (fun i => K.choose i * (N - K).choose (n - i))]
            exact_mod_cast Nat.sum_choose_mul_choose_eq N K n h_K]
      -- d⁻¹ * d = 1
      exact ENNReal.inv_mul_cancel h_denom_ne_zero h_denom_ne_top)

/-- Closed-form value of the hypergeometric PMF. -/
theorem hypergeometric_apply (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N)
    (k : Fin (n + 1)) :
    hypergeometric N K n h_n h_K k =
      (K.choose k.val * (N - K).choose (n - k.val) : ℕ) / (N.choose n : ℝ≥0∞) := by
  simp [hypergeometric]

/-- The hypergeometric PMF is non-zero iff the count is feasible:
both `k ≤ K` and `n - k ≤ N - K`. -/
theorem hypergeometric_apply_ne_zero_iff (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N)
    (k : Fin (n + 1)) :
    hypergeometric N K n h_n h_K k ≠ 0 ↔
      k.val ≤ K ∧ n - k.val ≤ N - K := by
  rw [hypergeometric_apply, ne_eq, ENNReal.div_eq_zero_iff]
  push_neg
  constructor
  · rintro ⟨h_num_ne_zero, _⟩
    have h_num_nat_ne_zero : K.choose k.val * (N - K).choose (n - k.val) ≠ 0 := by
      intro h_zero
      apply h_num_ne_zero
      exact_mod_cast h_zero
    have ⟨h1, h2⟩ := Nat.mul_ne_zero_iff.mp h_num_nat_ne_zero
    exact ⟨Nat.le_of_not_lt (mt Nat.choose_eq_zero_iff.mpr h1),
           Nat.le_of_not_lt (mt Nat.choose_eq_zero_iff.mpr h2)⟩
  · rintro ⟨h_kK, h_nkNK⟩
    refine ⟨?_, ENNReal.natCast_ne_top _⟩
    have h1 : K.choose k.val ≠ 0 := (Nat.choose_pos h_kK).ne'
    have h2 : (N - K).choose (n - k.val) ≠ 0 := (Nat.choose_pos h_nkNK).ne'
    exact_mod_cast Nat.mul_ne_zero h1 h2

/-- **`ENNReal.ofReal`-friendly closed form**: lifts the value to a single
`ENNReal.ofReal (rational)`, suitable for `norm_num` discharge. The
hypothesis `0 < N.choose n` is implied by `n ≤ N` but stated separately
to keep the theorem simp-friendly. -/
theorem hypergeometric_apply_eq_ofReal (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N)
    (k : Fin (n + 1)) :
    hypergeometric N K n h_n h_K k =
      ENNReal.ofReal
        ((K.choose k.val * (N - K).choose (n - k.val) : ℝ) / (N.choose n : ℝ)) := by
  rw [hypergeometric_apply]
  have h_pos : (0 : ℝ) < N.choose n := by exact_mod_cast Nat.choose_pos h_n
  rw [show ((K.choose k.val * (N - K).choose (n - k.val) : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((K.choose k.val * (N - K).choose (n - k.val) : ℝ)) from by
      push_cast; exact (ENNReal.ofReal_natCast _).symm,
      show ((N.choose n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (N.choose n : ℝ) from
        (ENNReal.ofReal_natCast _).symm,
      ← ENNReal.ofReal_div_of_pos h_pos]

/-- The kernel value at `k = 0`: `C(N - K, n) / C(N, n)`. -/
theorem hypergeometric_apply_zero (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N) :
    hypergeometric N K n h_n h_K ⟨0, Nat.lt_succ_of_le (Nat.zero_le _)⟩ =
      ((N - K).choose n : ℕ) / (N.choose n : ℝ≥0∞) := by
  rw [hypergeometric_apply]
  simp

/-- The kernel value at `k = n` (when `n ≤ K`): `C(K, n) / C(N, n)`. -/
theorem hypergeometric_apply_last (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N) :
    hypergeometric N K n h_n h_K ⟨n, Nat.lt_succ_self _⟩ =
      (K.choose n : ℕ) / (N.choose n : ℝ≥0∞) := by
  rw [hypergeometric_apply]
  simp

/-- Symmetry under `K ↔ N − K` and `k ↔ n − k`: complementary parameterization. -/
theorem hypergeometric_symm (N K n : ℕ) (h_n : n ≤ N) (h_K : K ≤ N)
    (k : Fin (n + 1)) :
    hypergeometric N (N - K) n h_n (Nat.sub_le _ _) k =
      hypergeometric N K n h_n h_K ⟨n - k.val, by omega⟩ := by
  rw [hypergeometric_apply, hypergeometric_apply]
  congr 1
  · push_cast
    rw [show N - (N - K) = K from by omega,
        show n - (n - k.val) = k.val from by have := k.isLt; omega,
        Nat.mul_comm]

end PMF
