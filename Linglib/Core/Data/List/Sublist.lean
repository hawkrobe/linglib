/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Pair sublists as positional order

`List.pair_sublist_iff_idxOf_lt`: on a `Nodup` list, `[a, b] <+ l` says exactly that
`a` and `b` are members with `a` at a strictly earlier index — the pair-sublist
relation is the strict linear order a duplicate-free list carries.
-/

namespace List

variable {α : Type*} [DecidableEq α] {a b : α} {l : List α}

theorem pair_sublist_of_idxOf_lt (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a < l.idxOf b) : [a, b] <+ l := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    by_cases hax : a = x
    · subst hax
      rcases mem_cons.mp hb with rfl | hb'
      · exact absurd h (Nat.lt_irrefl _)
      · exact (singleton_sublist.mpr hb').cons_cons a
    · have ha' : a ∈ xs := (mem_cons.mp ha).resolve_left hax
      have hbx : b ≠ x := by
        rintro rfl
        rw [idxOf_cons_self] at h
        exact Nat.not_lt_zero _ h
      have hb' : b ∈ xs := (mem_cons.mp hb).resolve_left hbx
      refine (ih ha' hb' ?_).cons x
      rw [idxOf_cons_ne _ (Ne.symm hax), idxOf_cons_ne _ (Ne.symm hbx)] at h
      exact Nat.lt_of_succ_lt_succ h

theorem idxOf_lt_of_pair_sublist (hnd : l.Nodup) (h : [a, b] <+ l) :
    l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [nodup_cons] at hnd
    obtain ⟨hx, hnd'⟩ := hnd
    cases h with
    | cons _ h' =>
      have ha : a ∈ xs := h'.subset (by simp)
      have hb : b ∈ xs := h'.subset (by simp)
      have hax : x ≠ a := by rintro rfl; exact hx ha
      have hbx : x ≠ b := by rintro rfl; exact hx hb
      rw [idxOf_cons_ne _ hax, idxOf_cons_ne _ hbx]
      exact Nat.succ_lt_succ (ih hnd' h')
    | cons_cons _ h' =>
      have hb : b ∈ xs := singleton_sublist.mp h'
      have hba : a ≠ b := by rintro rfl; exact hx hb
      rw [idxOf_cons_self, idxOf_cons_ne _ hba]
      exact Nat.succ_pos _

/-- On a `Nodup` list, the pair-sublist relation is the strict positional order. -/
theorem pair_sublist_iff_idxOf_lt (hnd : l.Nodup) :
    [a, b] <+ l ↔ a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b :=
  ⟨fun h => ⟨h.subset (by simp), h.subset (by simp), idxOf_lt_of_pair_sublist hnd h⟩,
   fun ⟨ha, hb, hlt⟩ => pair_sublist_of_idxOf_lt ha hb hlt⟩

end List
