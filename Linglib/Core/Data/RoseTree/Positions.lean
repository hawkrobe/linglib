module

public import Linglib.Core.Data.RoseTree.Get

/-!
# Positions of a rose tree

The positions of a rose tree `t` form `RoseTree.Positions t`, a subtype of `TreePath`. Since
`validPaths t` is prefix-closed, the positions inherit the order structure of `TreePath`: the root
is the least position, the parent of a position and the meet of two positions are again positions,
and strict dominance is well founded, so `Positions t` is a rooted tree in the sense of
`Mathlib/Order/SuccPred/Tree.lean`. Covering in `Positions t` is covering in `TreePath`
(`Positions.covBy_iff`), so the daughters of a position are its valid daughters.

The positions whose subtree satisfies a predicate form `RoseTree.positionsWhere P t`, decidable
when the predicate is, which picks out the positions of a label, of a branching node, or of any
other condition on a node and what it dominates. Replacing the subtree at a position leaves the
positions outside it where they were, for a predicate that does not look below the root
(`mem_positionsWhere_replaceAt`).

## Main declarations

* `RoseTree.Positions`: the positions of a tree, a rooted tree under the prefix order.
* `RoseTree.positionsWhere`: the positions whose subtree satisfies a predicate.
-/

@[expose] public section

namespace RoseTree

open Core.Order

variable {α : Type*}

/-- The valid positions of `t`, as a subtype of `TreePath`, form a rooted tree under the prefix
order. -/
abbrev Positions (t : RoseTree α) : Type := {p : TreePath // p ∈ t.validPaths}

namespace Positions

variable {t : RoseTree α}

/-- The root is the least position. -/
instance : OrderBot (Positions t) where
  bot := ⟨⊥, bot_mem_validPaths t⟩
  bot_le p := bot_le (a := p.val)

@[simp] theorem bot_val : ((⊥ : Positions t) : TreePath) = ⊥ := rfl

/-- The meet of two positions, their longest common prefix, is a position, since it dominates
either. -/
instance : SemilatticeInf (Positions t) :=
  Subtype.semilatticeInf fun _ _ hp _ ↦ validPaths_prefix_closed hp inf_le_left

@[simp] theorem inf_val (p q : Positions t) :
    ((p ⊓ q : Positions t) : TreePath) = p.val ⊓ q.val := rfl

/-- The parent of a position is a position. -/
instance : PredOrder (Positions t) where
  pred p := ⟨p.val.parent, validPaths_prefix_closed p.2 (TreePath.parent_le _)⟩
  pred_le p := TreePath.parent_le p.val
  min_of_le_pred {p} h := fun b hb ↦
    show p ≤ b from
      PredOrder.min_of_le_pred (α := TreePath)
        (show p.val ≤ Order.pred p.val from h)
        (show b.val ≤ p.val from hb)
  le_pred_of_lt {_ _} h :=
    TreePath.le_parent_of_lt (Subtype.coe_lt_coe.mpr h)

@[simp] theorem pred_val (p : Positions t) :
    ((Order.pred p : Positions t) : TreePath) = p.val.parent := rfl

/-- Covering in the positions of `t` is covering in `TreePath`, so the daughters of a position
are its valid daughters. -/
theorem covBy_iff {p q : Positions t} : p ⋖ q ↔ p.val ⋖ q.val := by
  constructor
  · intro h
    have hpred : q.val.parent = p.val := congrArg Subtype.val (Order.pred_eq_of_covBy h)
    have hc : Order.pred q.val ⋖ q.val :=
      Order.pred_covBy_of_not_isMin (not_isMin_of_lt (Subtype.coe_lt_coe.mpr h.lt))
    rwa [TreePath.pred_eq_parent, hpred] at hc
  · intro h
    have hpred : Order.pred q = p := Subtype.ext (by rw [pred_val]; exact Order.pred_eq_of_covBy h)
    have hpq : p < q := Subtype.coe_lt_coe.mp h.lt
    have hc : Order.pred q ⋖ q := Order.pred_covBy_of_not_isMin (not_isMin_of_lt hpq)
    rwa [hpred] at hc

end Positions

/-! ### Positions satisfying a predicate -/

section PositionsWhere

variable {P Q : RoseTree α → Prop} {t : RoseTree α} {p : TreePath}

/-- The positions of `t` whose subtree satisfies `P`. -/
def positionsWhere (P : RoseTree α → Prop) (t : RoseTree α) : Set TreePath :=
  {p | ∃ s ∈ t.subtreeAt p.toList, P s}

theorem mem_positionsWhere : p ∈ positionsWhere P t ↔ ∃ s ∈ t.subtreeAt p.toList, P s := Iff.rfl

instance [DecidablePred P] (t : RoseTree α) : DecidablePred (· ∈ positionsWhere P t) := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem positionsWhere_subset_validPaths (P : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere P t ⊆ t.validPaths := by
  rintro p ⟨s, hs, -⟩
  simp_all [validPaths, Option.mem_def]

theorem positionsWhere_mono (h : ∀ s, P s → Q s) (t : RoseTree α) :
    positionsWhere P t ⊆ positionsWhere Q t :=
  fun _ ⟨s, hs, hP⟩ ↦ ⟨s, hs, h s hP⟩

theorem positionsWhere_or (P Q : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere (fun s ↦ P s ∨ Q s) t = positionsWhere P t ∪ positionsWhere Q t := by
  ext p
  simp only [positionsWhere, Set.mem_ofPred_eq, Set.mem_union, and_or_left, exists_or]

theorem positionsWhere_and (P Q : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere (fun s ↦ P s ∧ Q s) t = positionsWhere P t ∩ positionsWhere Q t := by
  ext p
  simp only [positionsWhere, Set.mem_ofPred_eq, Set.mem_inter_iff, Option.mem_def]
  grind

/-- Relabelling moves the predicate onto the relabelled subtrees. -/
theorem positionsWhere_map {β : Type*} (f : α → β) (P : RoseTree β → Prop) (t : RoseTree α) :
    positionsWhere P (t.map f) = positionsWhere (fun s ↦ P (s.map f)) t := by
  ext p
  simp [positionsWhere, subtreeAt_map, Option.mem_def]

/-- Outside the replaced subtree, a position satisfies a predicate that ignores what lies below
the root exactly as before the replacement. -/
theorem mem_positionsWhere_replaceAt
    (hP : ∀ s i q (new : RoseTree α), P (s.replaceAt (i :: q) new) ↔ P s) {c : TreePath}
    (h : ¬ c ≤ p) (new : RoseTree α) :
    p ∈ positionsWhere P (t.replaceAt c.toList new) ↔ p ∈ positionsWhere P t := by
  by_cases hpc : p ≤ c
  · obtain ⟨_ | ⟨i, q⟩, hq⟩ := hpc
    · exact absurd (TreePath.le_def.mpr (by simp [← hq])) h
    rw [mem_positionsWhere, mem_positionsWhere, subtreeAt_replaceAt_of_prefix ⟨_, hq⟩, ← hq,
      List.drop_left]
    simp [hP]
  · rw [mem_positionsWhere, mem_positionsWhere, subtreeAt_replaceAt_of_not_prefix h hpc]

end PositionsWhere

end RoseTree
