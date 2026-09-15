import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.SplitIfs
import Mathlib.Order.Basic

/-!
# Injectivity of the decimal representation

This file proves that `Nat.repr`, the decimal string of a natural number, is injective,
through the injectivity of `Nat.toDigits 10`. `[UPSTREAM]` candidates for
`Init/Data/Nat/ToString.lean`.

## Main results

* `Nat.toDigits_ten_injective`
* `Nat.repr_injective`
-/

namespace Nat

theorem digitChar_eq_digitChar_iff : ∀ a < 10, ∀ b < 10, (digitChar a = digitChar b ↔ a = b) := by
  decide

theorem toDigits_ten_injective : Function.Injective (toDigits 10) := by
  intro m n h
  induction m using Nat.strongRecOn generalizing n with
  | _ m ih =>
  rw [toDigits_eq_ite (by omega), toDigits_eq_ite (n := n) (by omega)] at h
  split_ifs at h with hm hn hn
  · exact (digitChar_eq_digitChar_iff _ hm _ hn).mp (List.singleton_inj.mp h)
  · have hl := congrArg List.length h
    have := length_toDigits_pos (b := 10) (n := n / 10)
    simp at hl
  · have hl := congrArg List.length h
    have := length_toDigits_pos (b := 10) (n := m / 10)
    simp at hl
  · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    have h3 := ih (m / 10) (by omega) h1
    have h4 := (digitChar_eq_digitChar_iff _ (mod_lt m (by omega)) _ (mod_lt n (by omega))).mp
      (List.singleton_inj.mp h2)
    omega

theorem repr_injective : Function.Injective Nat.repr := λ m n h =>
  toDigits_ten_injective (by simpa [← toList_repr] using congrArg String.toList h)

end Nat
