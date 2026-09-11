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

/-- On a `Nodup` list, an element positioned between two elements of an infix belongs to the
infix. -/
theorem IsInfix.mem_of_idxOf_le_of_le {m : List α} {z : α} (hm : m <:+: l) (hnd : l.Nodup)
    (ha : a ∈ m) (hb : b ∈ m) (hz : z ∈ l) (haz : l.idxOf a ≤ l.idxOf z)
    (hzb : l.idxOf z ≤ l.idxOf b) : z ∈ m := by
  obtain ⟨s, t, rfl⟩ := hm
  rw [nodup_append, nodup_append] at hnd
  obtain ⟨⟨_, _, hsm⟩, _, hst⟩ := hnd
  have has : a ∉ s := λ h => hsm a h a ha rfl
  have hbs : b ∉ s := λ h => hsm b h b hb rfl
  rw [idxOf_append_of_mem (mem_append_right _ ha), idxOf_append_of_notMem has] at haz
  rw [idxOf_append_of_mem (mem_append_right _ hb), idxOf_append_of_notMem hbs] at hzb
  rcases mem_append.mp hz with hzsm | hzt
  · rcases mem_append.mp hzsm with hzs | hzm
    · have := idxOf_lt_length_iff.mpr hzs
      rw [idxOf_append_of_mem hzsm, idxOf_append_of_mem hzs] at haz
      omega
    · exact hzm
  · have hzsm : z ∉ s ++ m := λ h => hst z h z hzt rfl
    have := idxOf_lt_length_iff.mpr hb
    rw [idxOf_append_of_notMem hzsm, length_append] at hzb
    omega

end List
