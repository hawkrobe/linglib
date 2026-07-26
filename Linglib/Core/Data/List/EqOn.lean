/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Basic

/-!
# Positionwise agreement between lists

Two lists agree on a window of positions when their `getElem?` functions are
`Set.EqOn` that window. Agreement on `Set.Iic j` transports truncations
(`Set.EqOn.take_eq`), and agreement on `Set.Ici j` transports suffixes
(`Set.EqOn.drop_eq`).
-/

namespace List

variable {α : Type*} {u v : List α} {i j : ℕ}

/-- Prefixes agreeing below `i` have equal `i`-truncations. -/
theorem take_eq_of_agree (h : ∀ k, k < i → u[k]? = v[k]?) : u.take i = v.take i := by
  apply List.ext_getElem?
  intro k
  rcases lt_or_ge k i with hk | hk
  · simpa only [List.getElem?_take_of_lt hk] using h k hk
  · simp [List.getElem?_take_eq_none hk]

/-- Lists agreeing from `i` upward have equal `i`-suffixes. -/
theorem drop_eq_of_agree (h : ∀ k, i ≤ k → u[k]? = v[k]?) : u.drop i = v.drop i := by
  apply List.ext_getElem?
  intro k
  simpa only [List.getElem?_drop] using h (i + k) (Nat.le_add_right i k)

end List

namespace Set.EqOn

variable {α : Type*} {u v : List α} {i j : ℕ}

/-- The pointwise application of window agreement, stated in `getElem?` form so it
rewrites cleanly. -/
theorem getElem?_eq {s : Set ℕ} {k : ℕ} (h : Set.EqOn (u[·]?) (v[·]?) s) (hk : k ∈ s) :
    u[k]? = v[k]? := h hk

/-- Agreement on positions up to `j` transports truncations: `h.take_eq` for
`h : Set.EqOn (u[·]?) (v[·]?) (Set.Iic j)`. -/
theorem take_eq (h : Set.EqOn (u[·]?) (v[·]?) (Set.Iic j)) (hij : i ≤ j + 1) :
    u.take i = v.take i :=
  List.take_eq_of_agree fun _ hk => h (Set.mem_Iic.mpr (by omega))

/-- Agreement on positions from `j` transports suffixes: `h.drop_eq` for
`h : Set.EqOn (u[·]?) (v[·]?) (Set.Ici j)`. -/
theorem drop_eq (h : Set.EqOn (u[·]?) (v[·]?) (Set.Ici j)) (hij : j ≤ i) :
    u.drop i = v.drop i :=
  List.drop_eq_of_agree fun _ hk => h (Set.mem_Ici.mpr (by omega))

end Set.EqOn
