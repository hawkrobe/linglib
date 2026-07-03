/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Linglib.Core.Data.Setoid.Basic

/-!
# Round-to-multiple bounds and bucket refinement

Mirror of `Mathlib/Algebra/Order/ToIntervalMod.lean`: the additions a PR
there would make. [UPSTREAM]

A width-`ε` *bucket partition* of a scale is the kernel of `⌊·/ε⌋` — the
object linguistics calls scale granularity ([sauerland-stateva-2011],
[krifka-2007]). It is **not** the coset partition of `ε·ℤ`
(`AddSubgroup.zmultiples`): cosets collect residues, buckets collect
neighbours. Mathlib already provides the index and its bounds —
`toIcoDiv_eq_floor` identifies `toIcoDiv hε 0` with `⌊·/ε⌋`, and
`sub_floor_div_mul_nonneg`/`sub_floor_div_mul_lt` bound the cell — so this
file adds only what is missing: the error bound for rounding to the
*nearest* multiple of `ε`, and the refinement half of the finer-than order
on bucket partitions, derived from the kernel keystone
`Setoid.ker_le_ker_comp` via the floor-nesting identities
(`Nat.div_div_eq_div_mul`, `Int.floor_div_natCast`).

## Main results

- `abs_sub_round_div_zsmul_le`: rounding to the nearest multiple of `ε`
  moves a point by at most `ε / 2`
- `Setoid.ker_floor_div_le_natCast_mul`, `Nat.ker_div_le_of_dvd`: finer
  widths refine the bucket partition
-/

/-- Finer grain widths refine the bucket partition on ℕ: if `ε₁ ∣ ε₂`, the
`ε₁`-buckets sit inside the `ε₂`-buckets. -/
theorem Nat.ker_div_le_of_dvd {ε₁ ε₂ : ℕ} (h : ε₁ ∣ ε₂) :
    Setoid.ker (· / ε₁ : ℕ → ℕ) ≤ Setoid.ker (· / ε₂) := by
  obtain ⟨k, rfl⟩ := h
  simpa [Function.comp_def, Nat.div_div_eq_div_mul] using
    Setoid.ker_le_ker_comp (· / ε₁ : ℕ → ℕ) (· / k)

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α] {ε : α}

/-- Multiplying the width by a natural coarsens the bucket partition
`Setoid.ker ⌊·/ε⌋`: the refinement half of the finer-than order, via the
kernel keystone and `Int.floor_div_natCast`. -/
theorem Setoid.ker_floor_div_le_natCast_mul (ε : α) (k : ℕ) :
    Setoid.ker (fun d : α => ⌊d / ε⌋) ≤
      Setoid.ker (fun d : α => ⌊d / ((k : α) * ε)⌋) := by
  simpa [Function.comp_def, ← Int.floor_div_natCast, div_div,
    mul_comm ε (k : α)] using
    Setoid.ker_le_ker_comp (fun d : α => ⌊d / ε⌋) (· / (k : ℤ))

/-- Rounding to the nearest multiple of `ε` moves a point by at most
`ε / 2` — the sibling of `abs_sub_round` for multiples. -/
theorem abs_sub_round_div_zsmul_le (hε : 0 < ε) (d : α) :
    |d - round (d / ε) • ε| ≤ ε / 2 := by
  have h := abs_sub_round (d / ε)
  have key : d - round (d / ε) • ε = (d / ε - round (d / ε)) * ε := by
    rw [zsmul_eq_mul, sub_mul, div_mul_cancel₀ d hε.ne']
  rw [key, abs_mul, abs_of_pos hε]
  calc |d / ε - ↑(round (d / ε))| * ε ≤ 1 / 2 * ε :=
        mul_le_mul_of_nonneg_right h hε.le
    _ = ε / 2 := by ring
