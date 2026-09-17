/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.TakeDrop

/-!
# Membership and extensionality for `take` and `drop` by index

The `getElem?` forms of `List.mem_take_iff_getElem` and `List.mem_drop_iff_getElem`: an
element of a prefix or suffix is an entry of the original list at an index on that side of
the cut. Alongside, the extensionality lemmas `List.ext_take_getElem?` and
`List.ext_drop_getElem?`: two lists agreeing at every index below `n` have the same `take n`,
and agreeing from `n` on have the same `drop n`. [UPSTREAM] candidates for
`Init/Data/List/Nat/TakeDrop.lean`, beside their `getElem` counterparts and `List.ext_getElem?`.
-/

namespace List

variable {α : Type*} {l l₁ l₂ : List α} {a : α} {n : ℕ}

/-- An element of `l.take n` is an entry of `l` at an index below `n`. -/
theorem mem_take_iff_getElem? : a ∈ l.take n ↔ ∃ i < n, l[i]? = some a := by
  simp [mem_iff_getElem?, getElem?_take]

/-- An element of `l.drop n` is an entry of `l` at an index at least `n`. Unlike
`List.mem_drop_iff_getElem`, the index is into `l`, not into the suffix. -/
theorem mem_drop_iff_getElem? : a ∈ l.drop n ↔ ∃ i ≥ n, l[i]? = some a := by
  simp only [mem_iff_getElem?, getElem?_drop]
  exact ⟨fun ⟨i, h⟩ ↦ ⟨n + i, Nat.le_add_right n i, h⟩,
    fun ⟨i, hn, h⟩ ↦ ⟨i - n, by rwa [Nat.add_sub_cancel' hn]⟩⟩

/-- Lists agreeing at every index below `n` have the same prefix of length `n`. -/
theorem ext_take_getElem? (h : ∀ k < n, l₁[k]? = l₂[k]?) : l₁.take n = l₂.take n :=
  ext_getElem? fun k ↦ by
    rcases Nat.lt_or_ge k n with hk | hk
    · simpa only [getElem?_take_of_lt hk] using h k hk
    · simp [getElem?_take_eq_none hk]

/-- Lists agreeing at every index from `n` on have the same suffix from `n`. -/
theorem ext_drop_getElem? (h : ∀ k, n ≤ k → l₁[k]? = l₂[k]?) : l₁.drop n = l₂.drop n :=
  ext_getElem? fun k ↦ by simpa only [getElem?_drop] using h (n + k) (Nat.le_add_right n k)

/-- A nonempty suffix starts inside the list. -/
theorem lt_length_of_mem_drop (h : a ∈ l.drop n) : n < l.length :=
  Nat.not_le.mp (drop_eq_nil_iff.not.mp (ne_nil_of_mem h))

end List
