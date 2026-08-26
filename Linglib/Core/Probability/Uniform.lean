import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Linglib.Core.Order.Argmax

/-!
# The uniform vector on a finset

`Finset.uniform s` is the indicator of `s` scaled to a probability vector:
`(#s)⁻¹` on `s`, `0` off it, and the zero vector when `s` is empty — the
exact (ℚ-valued) uniform distribution as a plain function, for consumers that
compute with probability vectors rather than measures. `uniform_eq_indicator`
connects it to `Set.indicator`, and its inner products are mathlib's
`Finset.expect`: `∑ a, s.uniform a * f a = 𝔼 a ∈ s, f a`.

## Main definitions

* `Finset.uniform s` — `(#s)⁻¹` on `s`, `0` off it.

## Main statements

* `uniform_pos_iff`, `uniform_injective` — the support is `s`, and determines it.
* `sum_uniform_mul` — the inner product with `f` is the expectation of `f` on `s`.
* `sum_uniform_argmax_mul` — the expectation of `f` on its argmax is its maximum.
* `sum_mul_le_of_support` — a sub-probability average of `f` supported on `s` is
  at most the maximum of `f` on `s`.
-/

open scoped BigOperators

namespace Finset

variable {α K : Type*} [DecidableEq α] {s : Finset α} {a : α}

section Semifield

variable [Semifield K]

/-- The uniform vector on `s`: `(#s)⁻¹` on `s`, `0` off it. -/
def uniform (s : Finset α) : α → K := λ a => if a ∈ s then (s.card : K)⁻¹ else 0

theorem uniform_apply : s.uniform a = if a ∈ s then (s.card : K)⁻¹ else 0 := rfl

theorem uniform_eq_indicator :
    (s.uniform : α → K) = (s : Set α).indicator λ _ => (s.card : K)⁻¹ := by
  funext a; simp [uniform_apply, Set.indicator_apply]

@[simp] theorem uniform_of_mem (h : a ∈ s) : s.uniform a = (s.card : K)⁻¹ := if_pos h

@[simp] theorem uniform_of_notMem (h : a ∉ s) : s.uniform a = (0 : K) := if_neg h

variable [CharZero K]

/-- The inner product with the uniform vector is the expectation on `s`. -/
theorem sum_uniform_mul [Fintype α] (f : α → K) : ∑ a, s.uniform a * f a = 𝔼 a ∈ s, f a := by
  simp only [uniform_apply, ite_mul, zero_mul, sum_ite_mem, univ_inter, expect_eq_sum_div_card,
    div_eq_inv_mul, mul_sum]

theorem sum_uniform [Fintype α] : ∑ a, s.uniform a = if s = ∅ then (0 : K) else 1 := by
  have := sum_uniform_mul (s := s) (λ _ : α => (1 : K))
  simp only [mul_one] at this
  rw [this]; split_ifs with h
  · simp [h]
  · exact expect_const (nonempty_iff_ne_empty.mpr h) _

end Semifield

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem uniform_nonneg : (0 : K) ≤ s.uniform a := by
  rw [uniform_apply]; split_ifs <;> positivity

theorem uniform_le_one : s.uniform a ≤ (1 : K) := by
  rw [uniform_apply]; split_ifs with h
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast card_pos.mpr ⟨a, h⟩)
  · exact zero_le_one

theorem uniform_pos_iff : (0 : K) < s.uniform a ↔ a ∈ s := by
  rw [uniform_apply]; split_ifs with h
  · exact ⟨λ _ => h, λ _ => inv_pos.mpr (Nat.cast_pos.mpr (card_pos.mpr ⟨a, h⟩))⟩
  · exact ⟨λ h' => absurd h' (lt_irrefl 0), λ h' => absurd h' h⟩

/-- The uniform vector determines the finset. -/
theorem uniform_injective : Function.Injective (uniform : Finset α → α → K) := λ s t h =>
  Finset.ext λ a => by rw [← @uniform_pos_iff α K, h, uniform_pos_iff]

theorem sum_uniform_le_one [Fintype α] : ∑ a, s.uniform a ≤ (1 : K) := by
  rw [sum_uniform]; split_ifs <;> simp

/-- The expectation of `f` on its argmax is its maximum. -/
theorem sum_uniform_argmax_mul [Fintype α] (f : α → K) {a₀ : α} (h : a₀ ∈ s.argmax f) :
    ∑ a, (s.argmax f).uniform a * f a = f a₀ := by
  rw [sum_uniform_mul, expect_congr rfl (g := λ _ => f a₀) λ a ha => le_antisymm
    ((mem_argmax.mp h).2 a (mem_argmax.mp ha).1) ((mem_argmax.mp ha).2 a₀ (mem_argmax.mp h).1)]
  exact expect_const ⟨a₀, h⟩ _

/-- A sub-probability average of a nonnegative `f`, with weights supported on
`s`, is at most the maximum of `f` on `s`. -/
theorem sum_mul_le_of_support [Fintype α] (w f : α → K) (hw : ∀ a, 0 ≤ w a)
    (hsum : ∑ a, w a ≤ 1) (hsupp : ∀ a, a ∉ s → w a = 0) (hf : ∀ a, 0 ≤ f a) {a₀ : α}
    (h : a₀ ∈ s.argmax f) : ∑ a, w a * f a ≤ f a₀ :=
  calc ∑ a, w a * f a ≤ ∑ a, w a * f a₀ := sum_le_sum λ a _ => by
        by_cases ha : a ∈ s
        · exact mul_le_mul_of_nonneg_left ((mem_argmax.mp h).2 a ha) (hw a)
        · simp [hsupp a ha]
    _ = (∑ a, w a) * f a₀ := by rw [sum_mul]
    _ ≤ 1 * f a₀ := mul_le_mul_of_nonneg_right hsum (hf a₀)
    _ = f a₀ := one_mul _

end Finset
