/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Left- and right-zero elements

`IsLeftZero m` (`∀ a, m * a = m`) and `IsRightZero m` (`∀ a, a * m = m`) are the
semigroup-theoretic *left* and *right zeros*: the elements whose principal right,
resp. left, ideal is `{m}`. They are companions of `IsIdempotentElem` — every
one-sided zero is idempotent — and dual to each other under `MulOpposite`.

`[UPSTREAM]`: this would extend `Mathlib/Algebra/Group/Idempotent.lean`.
-/

variable {M : Type*}

section Mul
variable [Mul M] {a b : M}

/-- `m` is a **left zero**: `m * a = m` for every `a`. -/
def IsLeftZero (m : M) : Prop := ∀ a, m * a = m

/-- `m` is a **right zero**: `a * m = m` for every `a`. -/
def IsRightZero (m : M) : Prop := ∀ a, a * m = m

theorem isLeftZero_iff : IsLeftZero a ↔ ∀ b, a * b = a := Iff.rfl

theorem isRightZero_iff : IsRightZero a ↔ ∀ b, b * a = a := Iff.rfl

@[simp] theorem isLeftZero_op : IsLeftZero (MulOpposite.op a) ↔ IsRightZero a := by
  refine ⟨fun h c => MulOpposite.op_injective (h (.op c)), fun h c => ?_⟩
  obtain ⟨d, rfl⟩ := MulOpposite.op_surjective c
  exact congrArg MulOpposite.op (h d)

@[simp] theorem isRightZero_op : IsRightZero (MulOpposite.op a) ↔ IsLeftZero a := by
  refine ⟨fun h c => MulOpposite.op_injective (h (.op c)), fun h c => ?_⟩
  obtain ⟨d, rfl⟩ := MulOpposite.op_surjective c
  exact congrArg MulOpposite.op (h d)

/-- A left zero is idempotent. -/
theorem IsLeftZero.isIdempotentElem (h : IsLeftZero a) : IsIdempotentElem a := h a

/-- A right zero is idempotent. -/
theorem IsRightZero.isIdempotentElem (h : IsRightZero a) : IsIdempotentElem a := h a

/-- A left zero and a right zero coincide; in particular a two-sided zero is unique. -/
theorem IsLeftZero.eq_of_isRightZero (ha : IsLeftZero a) (hb : IsRightZero b) : a = b :=
  (ha b).symm.trans (hb a)

end Mul

section MulZeroClass
variable [MulZeroClass M]

@[simp] theorem isLeftZero_zero : IsLeftZero (0 : M) := fun _ => zero_mul _

@[simp] theorem isRightZero_zero : IsRightZero (0 : M) := fun _ => mul_zero _

end MulZeroClass
