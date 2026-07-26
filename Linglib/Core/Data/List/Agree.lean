/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

/-!
# Positionwise agreement between lists

`AgreeOn u v K` states that `u` and `v` have equal `getElem?` at every position in
`K`; `AgreeUpto` and `AgreeFrom` are its instances at down- and up-closed windows.
Agreement below `i` transports `i`-truncations (`AgreeUpto.take_eq`), and agreement
from `i` transports `i`-suffixes (`AgreeFrom.drop_eq`).
-/

namespace List

variable {α : Type*} {u v : List α} {i j : ℕ}

/-- `u` and `v` agree at every position in `K`. -/
def AgreeOn (u v : List α) (K : Set ℕ) : Prop := ∀ k ∈ K, u[k]? = v[k]?

/-- `u` and `v` agree at every index `≥ j`. -/
def AgreeFrom (u v : List α) (j : ℕ) : Prop := AgreeOn u v {k | j ≤ k}

/-- `u` and `v` agree at every index `≤ j`. -/
def AgreeUpto (u v : List α) (j : ℕ) : Prop := AgreeOn u v {k | k ≤ j}

theorem AgreeOn.mono {K K' : Set ℕ} (hKK' : K' ⊆ K) (h : AgreeOn u v K) :
    AgreeOn u v K' := fun k hk => h k (hKK' hk)

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

/-- Agreement up to `j` transports truncations: `h.take_eq` for `h : AgreeUpto u v j`. -/
theorem AgreeUpto.take_eq (h : AgreeUpto u v j) (hij : i ≤ j + 1) :
    u.take i = v.take i :=
  take_eq_of_agree fun k hk => h k (show k ≤ j by omega)

/-- Agreement from `j` transports suffixes: `h.drop_eq` for `h : AgreeFrom u v j`. -/
theorem AgreeFrom.drop_eq (h : AgreeFrom u v j) (hij : j ≤ i) : u.drop i = v.drop i :=
  drop_eq_of_agree fun k hk => h k (show j ≤ k by omega)

end List
