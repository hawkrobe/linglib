/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Infixes of a three-part concatenation

An infix of `u ++ m ++ v` lies within `u ++ m`, lies within `m ++ v`, or contains `m`. So an infix
no longer than `m` cannot contain both an element that occurs only in `u` and an element that
occurs only in `v`: this is the fact about short windows that pumping arguments use, when `m` is a
block of the pumped word that separates two others.

## Main results

* `List.IsInfix.infix_append_or_infix_append_or_infix`: an infix of `u ++ m ++ v` is an infix of
  `u ++ m` or of `m ++ v`, or contains `m`.
* `List.IsInfix.notMem_or_notMem_of_length_le`: an infix of `u ++ m ++ v` no longer than `m` misses
  every element occurring only in `u` or every element occurring only in `v`.

## Implementation notes

[UPSTREAM] candidate: `Mathlib/Data/List/Infix.lean`, or core `Init/Data/List/Sublist.lean` beside
`List.infix_append_iff`.
-/

@[expose] public section

namespace List

variable {α : Type*} {l u m v : List α} {x y : α}

/-- An infix of `u ++ m ++ v` is an infix of `u ++ m`, an infix of `m ++ v`, or contains `m`. -/
theorem IsInfix.infix_append_or_infix_append_or_infix (hl : l <:+: u ++ m ++ v) :
    l <:+: u ++ m ∨ l <:+: m ++ v ∨ m <:+: l := by
  obtain ⟨s, t, h⟩ := hl
  rw [append_assoc s, append_assoc u] at h
  obtain ⟨a', rfl, h₁⟩ | ⟨c', rfl, h₁⟩ := append_eq_append_iff.1 h
  · rw [← append_assoc] at h₁
    obtain ⟨c, h₂, rfl⟩ | ⟨c, rfl, rfl⟩ := append_eq_append_iff.1 h₁
    · exact .inl ⟨s, c, by rw [append_assoc s, ← h₂, append_assoc]⟩
    · exact .inr (.inr ⟨a', c, rfl⟩)
  · exact .inr (.inl ⟨c', t, by rw [append_assoc, h₁]⟩)

/-- An infix of `u ++ m ++ v` no longer than `m` misses an element that occurs only in `u` or an
element that occurs only in `v`. -/
theorem IsInfix.notMem_or_notMem_of_length_le (hl : l <:+: u ++ m ++ v)
    (hlen : l.length ≤ m.length) (hx : x ∉ m ++ v) (hy : y ∉ u ++ m) : x ∉ l ∨ y ∉ l := by
  rcases hl.infix_append_or_infix_append_or_infix with h | h | h
  · exact .inr fun hy' ↦ hy (h.subset hy')
  · exact .inl fun hx' ↦ hx (h.subset hx')
  · exact .inl fun hx' ↦ hx (mem_append_left v (h.eq_of_length_le hlen ▸ hx'))

end List
