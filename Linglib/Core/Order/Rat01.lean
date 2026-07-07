import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.NormNum
import Linglib.Core.Order.Comparison
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic

/-!
# Core/Scales/Rat01.lean — rational unit interval

A rational number in [0, 1] for gradient linguistic properties
(at-issueness, projectivity) and their contextual thresholds.

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).
-/

namespace Core.Order

-- ════════════════════════════════════════════════════
-- § 1a. Rational Unit Interval
-- ════════════════════════════════════════════════════

/-- A rational number in the unit interval [0, 1].

    Wraps Mathlib's `Set.Icc` subtype for gradient linguistic properties
    (at-issueness, projectivity, etc.) and their contextual thresholds.
    Using `Set.Icc` gives us standard interval infrastructure from Mathlib
    (order, membership, etc.) without custom boilerplate.

    Access: `r.val` for the rational value, `r.prop.1` for `0 ≤ r`,
    `r.prop.2` for `r ≤ 1`. -/
abbrev Rat01 := ↥(Set.Icc (0 : ℚ) 1)

namespace Rat01

/-- The rational value. -/
abbrev value (r : Rat01) : ℚ := r.val

/-- Proof that the value is non-negative. -/
theorem nonneg (r : Rat01) : 0 ≤ r.val := r.prop.1

/-- Proof that the value is at most 1. -/
theorem le_one (r : Rat01) : r.val ≤ 1 := r.prop.2

instance : Repr Rat01 where
  reprPrec r _ := repr r.val

/-- The endpoint 0. -/
def zero : Rat01 := ⟨0, by norm_num, by norm_num⟩

/-- The endpoint 1. -/
def one : Rat01 := ⟨1, by norm_num, by norm_num⟩

/-- The midpoint ½, the standard default threshold. -/
def half : Rat01 := ⟨1/2, by norm_num, by norm_num⟩

/-- Does the value strictly exceed a threshold? The `Rat01` face of
`Core.Order.Comparison.gt.over`. -/
def exceeds (d θ : Rat01) : Prop :=
  d ∈ Core.Order.Comparison.gt.over Subtype.val θ.val

instance (d θ : Rat01) : Decidable (exceeds d θ) :=
  inferInstanceAs (Decidable (θ.val < d.val))

/-- The complement `1 - r`, again in `[0, 1]`.

    Models the relationship between a gradient property and its dual on the
    same scale — e.g. not-at-issueness as the complement of at-issueness. -/
def compl (r : Rat01) : Rat01 :=
  ⟨1 - r.val, by linarith [r.le_one], by linarith [r.nonneg]⟩

@[simp] theorem compl_val (r : Rat01) : (compl r).val = 1 - r.val := rfl

@[simp] theorem compl_compl (r : Rat01) : compl (compl r) = r := by
  apply Subtype.ext; simp

theorem compl_zero : compl zero = one := by apply Subtype.ext; simp [zero, one]

theorem compl_one : compl one = zero := by apply Subtype.ext; simp [zero, one]

/-- The complement is order-reversing: a larger value has a smaller complement. -/
theorem compl_antitone : Antitone compl := by
  intro a b h
  show 1 - b.val ≤ 1 - a.val
  have : a.val ≤ b.val := h
  linarith

end Rat01

end Core.Order
