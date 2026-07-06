/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Multiset.Powerset
import Mathlib.Data.Multiset.Antidiagonal

/-!
# Counting pairs in `Multiset.antidiagonal`

`Multiset.antidiagonal w` enumerates the ordered splits `w = p.1 + p.2` *with
multiplicities*; this file computes them: the multiplicity of `(u, v)` is the product of
binomial coefficients `∏ x, (w.count x).choose (v.count x)` (and `0` off the diagonal
`u + v = w`).

## Main results

* `Multiset.count_antidiagonal`: the closed form for `(antidiagonal w).count (u, v)`.
* `Multiset.count_antidiagonal_eq_count_powerset`: the guard-free bridge
  `(antidiagonal (s + t)).count (s, t) = (s + t).powerset.count t`, reducing antidiagonal
  counting to `Multiset.count_powerset_of_le`.

`[UPSTREAM]` candidate; eventual mathlib home `Mathlib.Data.Multiset.Antidiagonal`, where
the closed form also evaluates `Finsupp.antidiagonal'`.

## Tags

multiset, antidiagonal, count, binomial coefficient
-/

namespace Multiset

variable {α : Type*} [DecidableEq α]

/-- The multiplicity of the ordered split `(s, t)` in `antidiagonal (s + t)` is the number
    of ways to select the sub-multiset `t` from `s + t`: `antidiagonal_eq_map_powerset`
    exhibits the antidiagonal as the powerset mapped through `u ↦ (s + t - u, u)`, which is
    injective in the second coordinate. -/
theorem count_antidiagonal_eq_count_powerset (s t : Multiset α) :
    (antidiagonal (s + t)).count (s, t) = (s + t).powerset.count t := by
  rw [antidiagonal_eq_map_powerset]
  have hpair : ((s + t - t, t) : Multiset α × Multiset α) = (s, t) := by
    rw [Multiset.add_sub_cancel_right]
  rw [← hpair]
  exact count_map_eq_count' _ _ (fun _ _ h => congrArg Prod.snd h) t

/-- Closed form for the multiplicities of `Multiset.antidiagonal`: an ordered split
    `(u, v)` of `w` occurs `∏ x, (w.count x).choose (v.count x)` times. -/
theorem count_antidiagonal (u v w : Multiset α) :
    (antidiagonal w).count (u, v) =
      if u + v = w then ∏ x ∈ w.toFinset, (w.count x).choose (v.count x) else 0 := by
  split_ifs with h
  · subst h
    rw [count_antidiagonal_eq_count_powerset, count_powerset_of_le (le_add_left v u)]
  · exact count_eq_zero.mpr fun hmem => h (mem_antidiagonal.mp hmem)

end Multiset
