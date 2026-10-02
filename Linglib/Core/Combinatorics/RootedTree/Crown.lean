/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Core.Data.UnorderedTree.Subtree

@[expose] public section

open RoseTree UnorderedTree

/-!
# Crowns of pruning cuts

The trees that occur in the crown of some pruning cut of `T` are exactly the proper subtrees of
`T`: a cut removes subtrees hanging below the root, and any one subtree below the root is removed
by the cut at its own edge. Hence `X` is not a subtree of `T` exactly when `T ≠ X` and no cut of
`T` has `X` in its crown.

## Main results

* `ConnesKreimer.exists_mem_crown_cutSummandsN_iff`: crown components are the proper subtrees.
* `ConnesKreimer.not_mem_subtrees_iff`: `X ∉ T.subtrees ↔ T ≠ X ∧ ∀ p ∈ cutSummandsN T, X ∉ p.1`.

## References

* [connes-kreimer-1998]
-/

namespace ConnesKreimer

variable {α : Type*}

/-! ### Crown components are proper subtrees -/

mutual

/-- Every crown component of a pruning cut of `t` is a subtree of a child of `t`. -/
theorem mk_mem_of_mem_crown_cutSummandsP :
    ∀ (t : RoseTree α), ∀ p ∈ cutSummandsP t, ∀ x ∈ p.1,
      UnorderedTree.mk x ∈ unorderedSubtreesList t.children
  | .node a cs => by
    intro p hp x hx
    rw [cutSummandsP_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact mk_mem_of_mem_crown_cutListSummandsP cs q hq x hx

/-- Every crown component of a pruning cut of a list of children is a subtree of one of them. -/
theorem mk_mem_of_mem_crown_cutListSummandsP :
    ∀ (cs : List (RoseTree α)), ∀ q ∈ cutListSummandsP cs, ∀ x ∈ q.1,
      UnorderedTree.mk x ∈ unorderedSubtreesList cs
  | [] => by
    intro q hq x hx
    rw [cutListSummandsP_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    exact absurd hx (Multiset.notMem_zero x)
  | t :: ts => by
    intro q hq x hx
    rw [cutListSummandsP_cons'] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have hx' : x ∈ pr.1.1 + pr.2.1 := by
      unfold combineP_fn at hx; split at hx <;> exact hx
    rw [unorderedSubtreesList, Multiset.mem_add]
    rcases Multiset.mem_add.mp hx' with h | h
    · exact .inl (mk_mem_of_mem_crown_augActionP t pr.1 ha x h)
    · exact .inr (mk_mem_of_mem_crown_cutListSummandsP ts pr.2 hq' x h)

/-- Every crown component of a per-child action on `t` is a subtree of `t`. -/
theorem mk_mem_of_mem_crown_augActionP :
    ∀ (t : RoseTree α), ∀ a ∈ augActionP t, ∀ x ∈ a.1,
      UnorderedTree.mk x ∈ unorderedSubtrees t
  | .node b cs => by
    intro a ha x hx
    rw [augActionP_eq] at ha
    rw [unorderedSubtrees, Multiset.mem_cons]
    rcases Multiset.mem_cons.mp ha with rfl | h
    · exact .inl (by rw [Multiset.mem_singleton.mp hx])
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      exact .inr (mk_mem_of_mem_crown_cutSummandsP (.node b cs) p hp x hx)

end

/-! ### Every proper subtree is a crown component -/

/-- The empty cut is a pruning cut. -/
theorem zero_mem_cutSummandsP (t : RoseTree α) :
    ((0 : Multiset (RoseTree α)), t) ∈ cutSummandsP t :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1.card = 0)
    ((cutSummandsP_filter_empty t).symm ▸ Multiset.mem_singleton_self _)

/-- The empty cut is a pruning cut of a list of children. -/
theorem zero_mem_cutListSummandsP (cs : List (RoseTree α)) :
    ((0 : Multiset (RoseTree α)), cs) ∈ cutListSummandsP cs :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1.card = 0)
    ((cutListSummandsP_filter_empty cs).symm ▸ Multiset.mem_singleton_self _)

/-- The empty cut is a per-child action. -/
theorem zero_mem_augActionP (t : RoseTree α) :
    ((0 : Multiset (RoseTree α)), some t) ∈ augActionP t :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1.card = 0)
    ((augActionP_filter_empty t).symm ▸ Multiset.mem_singleton_self _)

mutual

/-- Every subtree of a child of `t` is a crown component of some pruning cut of `t`. -/
theorem exists_mem_crown_cutSummandsP :
    ∀ (t : RoseTree α) (s : UnorderedTree α), s ∈ unorderedSubtreesList t.children →
      ∃ p ∈ cutSummandsP t, ∃ x ∈ p.1, UnorderedTree.mk x = s
  | .node a cs => fun s hs => by
    obtain ⟨q, hq, x, hx, rfl⟩ := exists_mem_crown_cutListSummandsP cs s hs
    exact ⟨(q.1, .node a q.2), by rw [cutSummandsP_node]; exact Multiset.mem_map_of_mem _ hq,
      x, hx, rfl⟩

/-- Every subtree of a child in the list is a crown component of some cut of the list. -/
theorem exists_mem_crown_cutListSummandsP :
    ∀ (cs : List (RoseTree α)) (s : UnorderedTree α), s ∈ unorderedSubtreesList cs →
      ∃ q ∈ cutListSummandsP cs, ∃ x ∈ q.1, UnorderedTree.mk x = s
  | [] => fun s hs => absurd hs (Multiset.notMem_zero s)
  | t :: ts => fun s hs => by
    rw [unorderedSubtreesList, Multiset.mem_add] at hs
    rcases hs with hs | hs
    · obtain ⟨a, ha, x, hx, rfl⟩ := exists_mem_crown_augActionP t s hs
      refine ⟨combineP_fn (a, (0, ts)), ?_, x, ?_, rfl⟩
      · rw [cutListSummandsP_cons']
        exact Multiset.mem_map_of_mem _
          (Multiset.mem_product.mpr ⟨ha, zero_mem_cutListSummandsP ts⟩)
      · unfold combineP_fn; split <;> simpa using hx
    · obtain ⟨q, hq, x, hx, rfl⟩ := exists_mem_crown_cutListSummandsP ts s hs
      refine ⟨combineP_fn ((0, some t), q), ?_, x, ?_, rfl⟩
      · rw [cutListSummandsP_cons']
        exact Multiset.mem_map_of_mem _
          (Multiset.mem_product.mpr ⟨zero_mem_augActionP t, hq⟩)
      · simpa [combineP_fn] using hx

/-- Every subtree of `t` is a crown component of some per-child action on `t`. -/
theorem exists_mem_crown_augActionP :
    ∀ (t : RoseTree α) (s : UnorderedTree α), s ∈ unorderedSubtrees t →
      ∃ a ∈ augActionP t, ∃ x ∈ a.1, UnorderedTree.mk x = s
  | .node b cs => fun s hs => by
    rw [unorderedSubtrees, Multiset.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨({.node b cs}, none), by rw [augActionP_eq]; exact Multiset.mem_cons_self _ _,
        _, Multiset.mem_singleton_self _, rfl⟩
    · obtain ⟨p, hp, x, hx, rfl⟩ := exists_mem_crown_cutSummandsP (.node b cs) s hs
      exact ⟨(p.1, some p.2), by
        rw [augActionP_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hp),
        x, hx, rfl⟩

end

/-- The crown components of the pruning cuts of `T` are exactly its proper subtrees. -/
theorem exists_mem_crown_cutSummandsN_iff {T X : UnorderedTree α} :
    (∃ p ∈ cutSummandsN T, X ∈ p.1) ↔ X ∈ T.subtrees ∧ X ≠ T := by
  induction T using Quotient.inductionOn with
  | h t =>
    obtain ⟨a, cs⟩ := t
    rw [quot_mk_eq_mk, subtrees_mk, unorderedSubtrees, Multiset.mem_cons]
    constructor
    · rintro ⟨p, hp, hX⟩
      refine ⟨.inr ?_, fun h ↦ cutSummandsN_self_not_mem_crown _ p hp (h ▸ hX)⟩
      rw [cutSummandsN_mk] at hp
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hX
      simpa using mk_mem_of_mem_crown_cutSummandsP _ q hq x hx
    · rintro ⟨hX | hX, hne⟩
      · exact absurd hX hne
      · obtain ⟨p, hp, x, hx, rfl⟩ := exists_mem_crown_cutSummandsP (.node a cs) _ hX
        exact ⟨projSummand p, by rw [cutSummandsN_mk]; exact Multiset.mem_map_of_mem _ hp,
          Multiset.mem_map_of_mem _ hx⟩

/-- `X` is not a subtree of `T` exactly when `T ≠ X` and no pruning cut of `T` has `X` in its
crown. -/
theorem not_mem_subtrees_iff {T X : UnorderedTree α} :
    X ∉ T.subtrees ↔ T ≠ X ∧ ∀ p ∈ cutSummandsN T, X ∉ p.1 := by
  constructor
  · intro h
    refine ⟨fun hTX ↦ h (hTX ▸ T.self_mem_subtrees), fun p hp hX ↦ h ?_⟩
    exact (exists_mem_crown_cutSummandsN_iff.mp ⟨p, hp, hX⟩).1
  · rintro ⟨hne, hcut⟩ hX
    by_cases hXT : X = T
    · exact hne hXT.symm
    · obtain ⟨p, hp, hXp⟩ := exists_mem_crown_cutSummandsN_iff.mpr ⟨hX, hXT⟩
      exact hcut p hp hXp

end ConnesKreimer
