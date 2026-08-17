import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum
import Linglib.Core.Order.Comparison

/-!
# The rational unit interval

`Rat01` is `↥(Set.Icc (0 : ℚ) 1)`, the home of gradient linguistic degrees
(at-issueness, projectivity, prior credence) and their contextual thresholds.
Mathlib's `unitInterval` is real-valued and topological, while linguistic degrees
are exact rationals, so this file instantiates the same interface at `ℚ`: the
algebraic structure and `0`, `1` come from
`Mathlib.Algebra.Order.Interval.Set.Instances`, and `symm` mirrors
`unitInterval.symm`.

`[UPSTREAM]` `symm` and its lemmas generalize verbatim to `Set.Icc (0 : β) 1`
over an ordered ring — a stated TODO of
`Mathlib.Algebra.Order.Interval.Set.Instances`.
-/

namespace Core.Order

/-- The unit interval of rationals — the `ℚ` counterpart of `unitInterval`. -/
abbrev Rat01 := ↥(Set.Icc (0 : ℚ) 1)

namespace Rat01

instance : Repr Rat01 where
  reprPrec r _ := repr r.val

instance : NeZero (1 : Rat01) := ⟨Set.Icc.coe_ne_zero.mp one_ne_zero⟩

/-- The midpoint ½, the standard default threshold. -/
def half : Rat01 := ⟨1/2, by norm_num, by norm_num⟩

/-- Does the value strictly exceed a threshold? The `Rat01` face of
    `Core.Order.Comparison.gt.over`. -/
def exceeds (d θ : Rat01) : Prop :=
  d ∈ Core.Order.Comparison.gt.over Subtype.val θ.val

instance (d θ : Rat01) : Decidable (exceeds d θ) :=
  inferInstanceAs (Decidable (θ.val < d.val))

/-- The involution `1 - r` — e.g. not-at-issueness from at-issueness. Mirrors
    `unitInterval.symm`. -/
def symm (r : Rat01) : Rat01 :=
  ⟨1 - r.val, Set.Icc.mem_iff_one_sub_mem.mp r.prop⟩

@[simp] theorem coe_symm_eq (r : Rat01) : (symm r).val = 1 - r.val := rfl

@[simp] theorem symm_symm (r : Rat01) : symm (symm r) = r :=
  Subtype.ext (by simp)

theorem symm_zero : symm 0 = 1 := Subtype.ext (by simp)

theorem symm_one : symm 1 = 0 := Subtype.ext (by simp)

theorem symm_involutive : Function.Involutive symm := symm_symm

theorem symm_bijective : Function.Bijective symm := symm_involutive.bijective

theorem symm_inj {r s : Rat01} : symm r = symm s ↔ r = s :=
  symm_bijective.injective.eq_iff

theorem symm_eq_one {r : Rat01} : symm r = 1 ↔ r = 0 := by rw [← symm_zero, symm_inj]

theorem symm_eq_zero {r : Rat01} : symm r = 0 ↔ r = 1 := by rw [← symm_one, symm_inj]

/-- `symm` is order-reversing. -/
theorem symm_antitone : Antitone symm := fun _ _ h =>
  Subtype.mk_le_mk.mpr (sub_le_sub_left (Subtype.coe_le_coe.mpr h) 1)

end Rat01

end Core.Order
