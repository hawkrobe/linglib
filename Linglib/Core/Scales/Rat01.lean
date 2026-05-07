import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.NormNum

/-!
# Core/Scales/Rat01.lean — rational unit interval

A rational number in [0, 1] for gradient linguistic properties
(at-issueness, projectivity) and their contextual thresholds.

This file is part of the Phase A decomposition of the legacy
`Core/Scales/Scale.lean` dumping ground (master plan v4).
-/

namespace Core.Scale

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

/-- Does the value strictly exceed a threshold? -/
def exceeds (d θ : Rat01) : Prop := θ.val < d.val

instance (d θ : Rat01) : Decidable (exceeds d θ) :=
  inferInstanceAs (Decidable (θ.val < d.val))

end Rat01

end Core.Scale
