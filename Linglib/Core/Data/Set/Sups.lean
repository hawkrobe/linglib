/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Suprema of pointwise sups

Mirror of `Mathlib/Data/Set/Sups.lean`. In a complete lattice, the supremum of `s ⊻ t` is the join
of the suprema of two nonempty sets. The indexed form of `s ⊻ t` is `Set.iSups s`, the set of
suprema of choices of an element from each member of a family `s`. [UPSTREAM]
-/

@[expose] public section

open SetFamily

namespace Set

variable {α : Type*} [CompleteLattice α] {s t : Set α}

/-- The supremum of `s ⊻ t` is `sSup s ⊔ sSup t` when `s` and `t` are nonempty. [UPSTREAM] -/
theorem sSup_sups (hs : s.Nonempty) (ht : t.Nonempty) : sSup (s ⊻ t) = sSup s ⊔ sSup t := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  refine le_antisymm (sSup_le <| forall_sups_iff.2 fun c hc d hd ↦
    sup_le_sup (le_sSup hc) (le_sSup hd)) (sup_le (sSup_le fun c hc ↦ ?_) (sSup_le fun d hd ↦ ?_))
  · exact le_sup_left.trans (le_sSup (sup_mem_sups hc hb))
  · exact le_sup_right.trans (le_sSup (sup_mem_sups ha hd))

section iSups

variable {ι : Type*} {s : ι → Set α} {a : α}

/-- The pointwise supremum of a family of sets is the set of suprema of choices of an element from
each member of the family. [UPSTREAM] -/
def iSups (s : ι → Set α) : Set α :=
  (fun f : ι → α ↦ ⨆ i, f i) '' univ.pi s

theorem mem_iSups : a ∈ iSups s ↔ ∃ f : ι → α, (∀ i, f i ∈ s i) ∧ ⨆ i, f i = a := by
  simp [iSups]

theorem iSup_mem_iSups {f : ι → α} (hf : ∀ i, f i ∈ s i) : ⨆ i, f i ∈ iSups s :=
  mem_iSups.2 ⟨f, hf, rfl⟩

/-- An element of one member of a family of nonempty sets lies below an element of their pointwise
supremum. [UPSTREAM] -/
theorem exists_mem_iSups_ge (hs : ∀ j, (s j).Nonempty) {i : ι} (ha : a ∈ s i) :
    ∃ b ∈ iSups s, a ≤ b := by
  classical
  let f : ι → α := Function.update (fun j ↦ (hs j).some) i a
  have hf : ∀ j, f j ∈ s j := fun j ↦ by
    by_cases h : j = i
    · subst h
      simpa [f] using ha
    · simpa [f, h] using (hs j).some_mem
  exact ⟨_, iSup_mem_iSups hf, by simpa [f] using le_iSup f i⟩

/-- The supremum of `Set.iSups s` is the supremum of the suprema of the `s i` when each is
nonempty. [UPSTREAM] -/
theorem sSup_iSups (hs : ∀ i, (s i).Nonempty) : sSup (iSups s) = ⨆ i, sSup (s i) := by
  refine le_antisymm (sSup_le fun _ ha ↦ ?_) (iSup_le fun i ↦ sSup_le fun b hb ↦ ?_)
  · obtain ⟨f, hf, rfl⟩ := mem_iSups.1 ha
    exact iSup_mono fun i ↦ le_sSup (hf i)
  · obtain ⟨c, hc, hbc⟩ := exists_mem_iSups_ge hs hb
    exact hbc.trans (le_sSup hc)

/-- The upper closure of `Set.iSups s` is the meet of the upper closures of the `s i`, as upper
sets. [UPSTREAM] -/
theorem upperClosure_iSups : upperClosure (iSups s) = ⨆ i, upperClosure (s i) := by
  refine SetLike.ext fun a ↦ ?_
  rw [mem_upperClosure, UpperSet.mem_iSup_iff]
  simp only [mem_upperClosure]
  refine ⟨fun ⟨_, hb, hba⟩ i ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := mem_iSups.1 hb
    exact ⟨f i, hf i, (le_iSup f i).trans hba⟩
  · choose f hf hfa using h
    exact ⟨_, iSup_mem_iSups hf, iSup_le hfa⟩

end iSups

end Set
