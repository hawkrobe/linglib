/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Linglib.Core.Data.Setoid.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# Grain partitions: interval-mod representatives and their buckets

Mirror of `Mathlib/Algebra/Order/ToIntervalMod.lean`, which this file
extends: `toIcoDiv hε 0` is the bucket index (`grainIndex_eq_toIcoDiv`),
and round-to-nearest-multiple is the centered-base representative.

A *grain* of width `ε` partitions a scale into the half-open cells
`[kε, (k+1)ε)` — the kernel of the bucket map `⌊·/ε⌋`. This is the
mathematical content of scale granularity: `grainIndex` is the bucket,
`grainFloor`/`grainRound` the canonical representatives (round down /
round to nearest), `grainCell` the cell, and `grainSetoid` the partition
as an equivalence, ordered by the `Setoid` refinement order. A grain is
**not** the coset partition of `ε·ℤ` (`AddSubgroup.zmultiples`): cosets
collect residues, cells collect neighbours.

The refinement facts derive from one keystone: a kernel refines the kernel
of anything that factors through it (`Setoid.ker_le_ker_comp`), applied to
the floor-nesting identities (`Nat.div_div_eq_div_mul`,
`Int.floor_div_natCast`).

`Nat.grainFloor` and `grainRound` are [UPSTREAM] candidates for this
file's mathlib original (the index is already `toIcoDiv` at base `0`,
`grainIndex_eq_toIcoDiv`, so an upstream PR should state the partition at
that generality); the `Setoid.ker` keystone lives in the
`Core/Data/Setoid/Basic.lean` mirror. Local `grain*` names are
domain-facing ([sauerland-stateva-2011] granularity); upstream names to be
derived at PR time.

## Main definitions

- `Nat.grainFloor`: round a natural down to a multiple of `ε`
- `Core.Order.grainIndex`, `grainFloor`, `grainRound`, `grainCell`,
  `grainSetoid`: the field-valued grain

## Main results

- `Nat.ker_div_le_of_dvd`, `Core.Order.grainSetoid_le_natCast_mul`:
  finer widths refine the partition
- `Core.Order.mem_grainCell_self`, `abs_sub_grainRound_le`: representative
  and error bounds
-/

/-- Round a natural number down to a multiple of `ε` — the canonical
representative of its grain cell. [UPSTREAM] -/
def Nat.grainFloor (ε n : ℕ) : ℕ := n / ε * ε

theorem Nat.grainFloor_le (ε n : ℕ) : Nat.grainFloor ε n ≤ n :=
  Nat.div_mul_le_self n ε

theorem Nat.grainFloor_dvd (ε n : ℕ) : ε ∣ Nat.grainFloor ε n :=
  Dvd.intro_left _ rfl

/-- Finer grain widths refine the bucket partition on ℕ: if `ε₁ ∣ ε₂`, the
`ε₁`-cells sit inside the `ε₂`-cells. -/
theorem Nat.ker_div_le_of_dvd {ε₁ ε₂ : ℕ} (h : ε₁ ∣ ε₂) :
    Setoid.ker (· / ε₁ : ℕ → ℕ) ≤ Setoid.ker (· / ε₂) := by
  obtain ⟨k, rfl⟩ := h
  have hfac : (· / (ε₁ * k) : ℕ → ℕ) = (· / k) ∘ (· / ε₁) :=
    funext fun n => (Nat.div_div_eq_div_mul n ε₁ k).symm
  rw [hfac]
  exact Setoid.ker_le_ker_comp _ _

namespace Core.Order

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α] {ε : α}

/-- The index of the grain cell containing `d`: the `k` with
`d ∈ [kε, (k+1)ε)`. -/
def grainIndex (ε d : α) : ℤ := ⌊d / ε⌋

/-- The lower representative of `d`'s grain cell: round down to a multiple
of `ε`. -/
def grainFloor (ε d : α) : α := grainIndex ε d • ε

/-- Round `d` to the nearest multiple of `ε`. [UPSTREAM] as a `round`
sibling. -/
def grainRound (ε d : α) : α := round (d / ε) • ε

/-- The half-open grain cell containing `d`. -/
def grainCell (ε d : α) : Set α := Set.Ico (grainFloor ε d) (grainFloor ε d + ε)

/-- The grain partition as an equivalence: same cell. -/
def grainSetoid (ε : α) : Setoid α := Setoid.ker (grainIndex ε)

theorem grainFloor_le (hε : 0 < ε) (d : α) : grainFloor ε d ≤ d := by
  rw [grainFloor, grainIndex, zsmul_eq_mul, ← le_div_iff₀ hε]
  exact Int.floor_le _

theorem lt_grainFloor_add (hε : 0 < ε) (d : α) : d < grainFloor ε d + ε := by
  have h := Int.lt_floor_add_one (d / ε)
  calc d = d / ε * ε := (div_mul_cancel₀ d hε.ne').symm
    _ < (⌊d / ε⌋ + 1) * ε := by
        exact mul_lt_mul_of_pos_right (by exact_mod_cast h) hε
    _ = grainFloor ε d + ε := by
        rw [grainFloor, grainIndex, zsmul_eq_mul]; ring

/-- Every degree lies in its own grain cell. -/
theorem mem_grainCell_self (hε : 0 < ε) (d : α) : d ∈ grainCell ε d :=
  ⟨grainFloor_le hε d, lt_grainFloor_add hε d⟩

/-- The grain index is mathlib's `toIcoDiv` at base point `0`: the unique
multiple count landing `d` in `[0, ε)` after subtraction. `toIcoDiv` is the
more general object (archimedean ordered groups, no division); `grainIndex`
is its computation-friendly `FloorRing` form. -/
theorem grainIndex_eq_toIcoDiv (hε : 0 < ε) (d : α) :
    grainIndex ε d = toIcoDiv hε 0 d := by
  refine (toIcoDiv_eq_of_sub_zsmul_mem_Ico hε ?_).symm
  rw [Set.mem_Ico, zero_add, sub_nonneg, sub_lt_iff_lt_add']
  exact ⟨grainFloor_le hε d, lt_grainFloor_add hε d⟩

/-- Multiplying the width by a natural coarsens the partition: the
refinement half of the finer-than order, via the kernel keystone and
`Int.floor_div_natCast`. -/
theorem grainSetoid_le_natCast_mul (ε : α) (k : ℕ) :
    grainSetoid ε ≤ grainSetoid ((k : α) * ε) := by
  have hfac : grainIndex ((k : α) * ε) = (· / (k : ℤ)) ∘ grainIndex ε := by
    funext d
    show ⌊d / ((k : α) * ε)⌋ = ⌊d / ε⌋ / (k : ℤ)
    rw [mul_comm (k : α) ε, ← div_div, ← Int.floor_div_natCast]
  rw [grainSetoid, grainSetoid, hfac]
  exact Setoid.ker_le_ker_comp _ _

/-- Rounding to the nearest multiple of `ε` moves a degree by at most
`ε / 2` — the error bound behind halo widths. -/
theorem abs_sub_grainRound_le (hε : 0 < ε) (d : α) :
    |d - grainRound ε d| ≤ ε / 2 := by
  have h := abs_sub_round (d / ε)
  have key : d - grainRound ε d = (d / ε - round (d / ε)) * ε := by
    rw [grainRound, zsmul_eq_mul, sub_mul, div_mul_cancel₀ d hε.ne']
  rw [key, abs_mul, abs_of_pos hε]
  calc |d / ε - ↑(round (d / ε))| * ε ≤ 1 / 2 * ε :=
        mul_le_mul_of_nonneg_right h hε.le
    _ = ε / 2 := by ring

end Core.Order
