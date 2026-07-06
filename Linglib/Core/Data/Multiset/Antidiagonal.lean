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
multiplicities*; this file computes those multiplicities: `(u, v)` occurs
`∏ x, (w.count x).choose (v.count x)` times when `u + v = w`, and `0` times otherwise.

## Main results

* `Multiset.count_antidiagonal`: the closed form for `(antidiagonal w).count (u, v)`.
* `Multiset.count_antidiagonal_eq_count_powerset`: the guard-free bridge to
  `Multiset.count_powerset_of_le`.
* `Multiset.count_antidiagonal_swap`: the multiplicity is symmetric in the two slots.

`[UPSTREAM]` candidate; eventual mathlib home `Mathlib.Data.Multiset.Antidiagonal`, where
the closed form also evaluates `Finsupp.antidiagonal'`.

-/

namespace Multiset

variable {α : Type*}

/-- `antidiagonal` is invariant under `Prod.swap`: commutativity of `+` permutes the
    ordered splits. -/
theorem antidiagonal_swap (s : Multiset α) :
    s.antidiagonal.map Prod.swap = s.antidiagonal := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a t ih =>
    simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.map_map,
      ← Prod.map_comp_swap, ← Multiset.map_map _ Prod.swap, ih, add_comm]

variable [DecidableEq α]

/-- The multiplicity of `(s, t)` in `antidiagonal (s + t)` is the number of ways to
    select the sub-multiset `t` from `s + t`. -/
theorem count_antidiagonal_eq_count_powerset (s t : Multiset α) :
    (antidiagonal (s + t)).count (s, t) = (s + t).powerset.count t := by
  rw [antidiagonal_eq_map_powerset,
      show (s, t) = (s + t - t, t) by rw [Multiset.add_sub_cancel_right]]
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

/-- The antidiagonal multiplicity is symmetric in the two slots. -/
theorem count_antidiagonal_swap (u v w : Multiset α) :
    (antidiagonal w).count (u, v) = (antidiagonal w).count (v, u) := by
  conv_lhs => rw [← antidiagonal_swap w]
  exact count_map_eq_count' _ _ Prod.swap_injective (v, u)

end Multiset
