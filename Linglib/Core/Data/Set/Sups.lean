/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Suprema of pointwise sups

Mirror of `Mathlib/Data/Set/Sups.lean`: in a complete lattice, the supremum of `s ⊻ t` is the
join of the suprema of two nonempty sets. [UPSTREAM]
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

end Set
