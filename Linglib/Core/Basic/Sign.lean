module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Opposite signs

When two elements have opposite signs, and when two differences from a common point do: exactly
when the point lies strictly between the two elements, or all three coincide.

## Main results

* `sign_eq_neg_sign_iff`: two elements have opposite signs when they lie strictly on opposite
  sides of zero or both vanish.
* `sign_sub_eq_neg_sign_sub_iff`: `a - c` and `b - c` have opposite signs when `c` lies strictly
  between `a` and `b`, or `a = b = c`.
-/

@[expose] public section

variable {α : Type*}

theorem sign_eq_neg_sign_iff [Zero α] [LinearOrder α] {x y : α} :
    SignType.sign x = -SignType.sign y ↔ x < 0 ∧ 0 < y ∨ 0 < x ∧ y < 0 ∨ x = 0 ∧ y = 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [sign_neg, sign_pos, lt_asymm, ne_of_lt, ne_of_gt]

theorem sign_sub_eq_neg_sign_sub_iff [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {a b c : α} :
    SignType.sign (a - c) = -SignType.sign (b - c) ↔ c ∈ Set.uIoo a b ∨ a = c ∧ b = c := by
  rw [sign_eq_neg_sign_iff]
  simp only [Set.uIoo, Set.mem_Ioo, inf_lt_iff, lt_sup_iff, sub_neg, sub_pos, sub_eq_zero]
  grind
