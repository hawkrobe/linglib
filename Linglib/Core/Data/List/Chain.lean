/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Chain

/-!
# Lemmas about `List.IsChain`

Three `List.IsChain` facts whose `List.Pairwise` counterparts are in `Init/Data/List/Pairwise.lean`
but which `Mathlib/Data/List/Chain.lean` lacks. [UPSTREAM] candidates for that file.

## Main results

* `List.isChain_of_forall`: a relation that holds everywhere makes every list a chain, mirroring
  `List.pairwise_of_forall`.
* `List.isChain_and_iff` and `List.IsChain.and`: a chain for a conjunction of relations is
  exactly a chain for each conjunct, mirroring `List.pairwise_and_iff` and `List.Pairwise.and`.
-/

@[expose] public section

namespace List

variable {α : Type*} {R S T : α → α → Prop} {l : List α}

theorem isChain_of_forall (H : ∀ x y, R x y) : IsChain R l := (pairwise_of_forall H).isChain

theorem isChain_and_iff :
    l.IsChain (fun a b ↦ S a b ∧ T a b) ↔ l.IsChain S ∧ l.IsChain T := by
  simp [isChain_iff_getElem, forall_and]

theorem IsChain.and (hS : l.IsChain S) (hT : l.IsChain T) : l.IsChain fun a b ↦ S a b ∧ T a b :=
  isChain_and_iff.2 ⟨hS, hT⟩

end List
