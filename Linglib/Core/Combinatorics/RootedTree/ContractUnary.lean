/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Nonplanar

/-!
# Contracting unary vertices of a rose tree

`contractUnary` collapses every unary vertex (one with exactly one child) into that
child — the series reduction normalizing a rooted tree to one with no unary vertices.
Each contracted vertex disappears whole, so the vertex count drops by exactly the
number of unary vertices.

## Main definitions

* `RoseTree.contractUnary`, `RoseTree.numUnary`: the contraction and the unary-vertex
  count, with descents to the `Nonplanar` quotient.

## Main results

* `RoseTree.numUnary_contractUnary`: the result has no unary vertices.
* `RoseTree.contractUnary_eq_self_iff`: the fixed points are exactly the unary-free
  trees; hence `contractUnary_idem`.
* `RoseTree.numNodes_contractUnary_add_numUnary`: each contraction removes one vertex.

`[UPSTREAM]` candidate alongside the `RoseTree` carrier.

## Tags

rose tree, unary vertex, contraction, series reduction
-/

namespace RoseTree

variable {α : Type*} (a : α) (c d : RoseTree α) (cs : List (RoseTree α))

/-! ### The contraction -/

/-- Rebuild a node from already-contracted children: a lone child replaces the node,
    otherwise the node is kept. -/
private def contractCombine : List (RoseTree α) → RoseTree α
  | [c] => c
  | cs  => node a cs

private theorem contractCombine_cons₂ :
    contractCombine a (c :: d :: cs) = node a (c :: d :: cs) := rfl

/-- Contract every unary (single-child) vertex into its child. -/
def contractUnary : RoseTree α → RoseTree α :=
  fold contractCombine

private theorem contractUnary_node :
    contractUnary (node a cs) = contractCombine a (cs.map contractUnary) := by
  simp only [contractUnary, fold_node]

@[simp] theorem contractUnary_leaf : contractUnary (leaf a) = leaf a := rfl

@[simp] theorem contractUnary_node_singleton :
    contractUnary (node a [c]) = contractUnary c := rfl

@[simp] theorem contractUnary_node_cons₂ :
    contractUnary (node a (c :: d :: cs)) =
      node a (contractUnary c :: contractUnary d :: cs.map contractUnary) := by
  rw [contractUnary_node, List.map_cons, List.map_cons, contractCombine_cons₂]

/-- The number of unary (single-child) vertices. -/
def numUnary : RoseTree α → ℕ :=
  fold fun _ ns => (if ns.length = 1 then 1 else 0) + ns.sum

@[simp] theorem numUnary_node :
    numUnary (node a cs) = (if cs.length = 1 then 1 else 0) + (cs.map numUnary).sum := by
  simp only [numUnary, fold_node, List.length_map]

/-! ### Vertex-count conservation -/

/-- Conservation at one vertex: `contractCombine` loses the root exactly when unary. -/
private theorem numNodes_contractCombine_add :
    (contractCombine a cs).numNodes + (if cs.length = 1 then 1 else 0)
      = 1 + (cs.map numNodes).sum := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩ <;> simp [contractCombine, Nat.add_comm]

/-- Each contracted unary vertex removes exactly one vertex. -/
theorem numNodes_contractUnary_add_numUnary (t : RoseTree α) :
    (contractUnary t).numNodes + t.numUnary = t.numNodes := by
  induction t with
  | node a cs ih =>
    have key : ((cs.map contractUnary).map numNodes).sum + (cs.map numUnary).sum
        = (cs.map numNodes).sum := by
      rw [List.map_map, ← List.sum_map_add]
      exact congrArg List.sum (List.map_congr_left ih)
    have hroot := numNodes_contractCombine_add a (cs.map contractUnary)
    rw [List.length_map] at hroot
    rw [contractUnary_node, numUnary_node, numNodes_node]
    omega

/-! ### `contractUnary` normalizes: no unary vertices remain -/

private theorem numUnary_contractCombine (h : ∀ c ∈ cs, c.numUnary = 0) :
    (contractCombine a cs).numUnary = 0 := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · rfl
  · exact h c List.mem_cons_self
  · rw [contractCombine_cons₂, numUnary_node, if_neg (by simp only [List.length_cons]; omega),
      Nat.zero_add]
    exact List.sum_eq_zero fun n hn => by
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hn
      exact h c' hc'

/-- After contraction no unary vertices remain. -/
@[simp] theorem numUnary_contractUnary (t : RoseTree α) : (contractUnary t).numUnary = 0 := by
  induction t with
  | node a cs ih =>
    rw [contractUnary_node]
    exact numUnary_contractCombine a _ fun c hc => by
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

private theorem eq_zero_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) {n : ℕ} (hn : n ∈ l) :
    n = 0 := by
  induction l with
  | nil => cases hn
  | cons x xs ih =>
    rw [List.sum_cons] at h
    rcases List.mem_cons.mp hn with rfl | hmem
    · omega
    · exact ih (by omega) hmem

/-- The fixed points of `contractUnary` are exactly the unary-free trees. -/
theorem contractUnary_eq_self_iff {t : RoseTree α} :
    contractUnary t = t ↔ t.numUnary = 0 := by
  refine ⟨fun h => h ▸ numUnary_contractUnary t, fun h => ?_⟩
  induction t with
  | node a cs ih =>
    rw [numUnary_node] at h
    have hlen : cs.length ≠ 1 := by
      intro hl
      rw [if_pos hl] at h
      omega
    rw [if_neg hlen, Nat.zero_add] at h
    have hch : ∀ c ∈ cs, c.numUnary = 0 := fun c hc =>
      eq_zero_of_sum_eq_zero h (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hmap : cs.map contractUnary = cs := by
      conv_rhs => rw [← List.map_id cs]
      exact List.map_congr_left fun c hc => ih c hc (hch c hc)
    rw [contractUnary_node, hmap]
    rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
    · rfl
    · exact absurd rfl hlen
    · rfl

/-- `contractUnary` is idempotent. -/
@[simp] theorem contractUnary_idem (t : RoseTree α) :
    contractUnary (contractUnary t) = contractUnary t :=
  contractUnary_eq_self_iff.mpr (numUnary_contractUnary t)

/-! ### `Perm` invariance -/

/-- `numUnary` is a `Perm`-invariant. -/
theorem numUnary_perm {t s : RoseTree α} (h : Perm t s) : t.numUnary = s.numUnary :=
  fold_perm (fun _ _ _ h' => by rw [h'.length_eq, h'.sum_eq]) h

private theorem contractCombine_perm :
    ∀ {L₁ L₂ : List (RoseTree α)}, PermList L₁ L₂ →
      Perm (contractCombine a L₁) (contractCombine a L₂)
  | _, _, .nil => Perm.refl _
  | _, _, @PermList.cons _ _ _ cs ds h hs =>
    match cs, ds, hs.length_eq, hs with
    | [], [], _, _ => h
    | _ :: _, _ :: _, _, hs' => .node (.cons h hs')
    | [], _ :: _, hlen, _ => by simp at hlen
    | _ :: _, [], hlen, _ => by simp at hlen
  | _, _, .swap c d cs => .node (.swap c d cs)
  | _, _, .trans h₁ h₂ => (contractCombine_perm h₁).trans (contractCombine_perm h₂)

/-- `contractUnary` respects `Perm`: contraction descends to the nonplanar quotient
    (`fold_rel` at `S := Perm`, fed by the combinator congruence). -/
theorem Perm.contractUnary {t s : RoseTree α} (h : Perm t s) :
    Perm t.contractUnary s.contractUnary :=
  fold_rel Perm.refl (fun h₁ h₂ => h₁.trans h₂)
    (fun a {_ _} h' => contractCombine_perm a (PermList.of_rel h')) h

end RoseTree

/-! ### Descent to `Nonplanar` -/

namespace RootedTree.Nonplanar

variable {α : Type*}

/-- The number of unary vertices of a nonplanar tree. -/
def numUnary : Nonplanar α → ℕ :=
  Nonplanar.lift RoseTree.numUnary fun _ _ h => RoseTree.numUnary_perm h

@[simp] theorem numUnary_mk (t : RoseTree α) : (mk t).numUnary = t.numUnary := rfl

/-- Contract every unary vertex into its child. -/
def contractUnary : Nonplanar α → Nonplanar α :=
  Quotient.map RoseTree.contractUnary fun _ _ h => h.contractUnary

@[simp] theorem contractUnary_mk (t : RoseTree α) :
    contractUnary (mk t) = mk t.contractUnary := rfl

/-- Each contracted unary vertex removes exactly one vertex. -/
theorem numNodes_contractUnary_add_numUnary (t : Nonplanar α) :
    (contractUnary t).numNodes + t.numUnary = t.numNodes :=
  Quotient.inductionOn t fun p => RoseTree.numNodes_contractUnary_add_numUnary p

/-- After contraction no unary vertices remain. -/
@[simp] theorem numUnary_contractUnary (t : Nonplanar α) : (contractUnary t).numUnary = 0 :=
  Quotient.inductionOn t fun p => RoseTree.numUnary_contractUnary p

/-- `contractUnary` is idempotent. -/
@[simp] theorem contractUnary_idem (t : Nonplanar α) :
    contractUnary (contractUnary t) = contractUnary t :=
  Quotient.inductionOn t fun p => congrArg mk (RoseTree.contractUnary_idem p)

end RootedTree.Nonplanar
