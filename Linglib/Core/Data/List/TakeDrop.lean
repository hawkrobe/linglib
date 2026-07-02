/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.TakeDrop

/-!
# Membership in `take` and `drop`, positionally

`getElem?`-indexed characterizations of membership in a prefix or suffix. Candidates
for `Mathlib/Data/List/TakeDrop.lean`.
-/

namespace List

variable {α : Type*} {a : α} {w : List α} {k : ℕ}

theorem mem_take_iff : a ∈ w.take k ↔ ∃ j < k, w[j]? = some a := by
  simp [List.mem_iff_getElem?, List.getElem?_take]

theorem mem_drop_iff : a ∈ w.drop k ↔ ∃ j ≥ k, w[j]? = some a := by
  simp only [List.mem_iff_getElem?, List.getElem?_drop]
  exact ⟨fun ⟨t, ht⟩ => ⟨k + t, Nat.le_add_right k t, ht⟩,
    fun ⟨j, hkj, hj⟩ => ⟨j - k, by rwa [Nat.add_sub_cancel' hkj]⟩⟩

end List
