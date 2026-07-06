/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Core.Data.RoseTree.Nonplanar

/-!
# Size measures on forests of rooted nonplanar trees

For a forest `F : Multiset (Nonplanar α)`: `b₀` counts component trees, `alpha` counts
non-root vertices (equivalently, edges), and `sigma = b₀ + alpha` is the total vertex
count (`sigma_eq_sum_numNodes`) — the forest case of `#V = b₀ + #E`.

## Main definitions

* `RootedTree.Nonplanar.accCount`: the non-root vertex count `numNodes - 1` of a tree.
* `RootedTree.Forest.b₀`: the number of component trees.
* `RootedTree.Forest.alpha`: the total non-root vertex count.
* `RootedTree.Forest.sigma`: `b₀ + alpha`.

## Main results

* `RootedTree.Forest.sigma_eq_sum_numNodes`: `sigma F = (F.map numNodes).sum`.

`[UPSTREAM]` candidate alongside the `Nonplanar` carrier.
-/

namespace RootedTree

namespace Nonplanar

variable {α : Type*}

/-- The number of non-root vertices of a rooted tree, `numNodes - 1` (equivalently, its
    edge count). -/
def accCount (t : Nonplanar α) : ℕ := t.numNodes - 1

@[simp] theorem accCount_leaf (a : α) : (leaf a : Nonplanar α).accCount = 0 := by
  simp [accCount]

theorem accCount_eq_numNodes_sub_one (t : Nonplanar α) : t.accCount = t.numNodes - 1 := rfl

/-- `accCount + 1` recovers the vertex count. -/
theorem accCount_add_one (t : Nonplanar α) : t.accCount + 1 = t.numNodes :=
  Nat.succ_pred_eq_of_pos t.numNodes_pos

/-- `accCount` at a node is the total vertex count of the children. -/
theorem accCount_node (a : α) (F : Multiset (Nonplanar α)) :
    (node a F).accCount = (F.map numNodes).sum := by
  simp [accCount]

/-- Adjoining a root above a pair of trees adds two non-root vertices. -/
theorem accCount_node_pair (a : α) (l r : Nonplanar α) :
    (node a {l, r}).accCount = l.accCount + r.accCount + 2 := by
  rw [accCount_node]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, ← accCount_add_one]
  omega

end Nonplanar

/-! ### Forest measures -/

namespace Forest

variable {α : Type*}

/-- The number of component trees of a forest (its zeroth Betti number). -/
def b₀ (F : Multiset (Nonplanar α)) : ℕ := Multiset.card F

@[simp] theorem b₀_zero : b₀ (0 : Multiset (Nonplanar α)) = 0 := Multiset.card_zero
@[simp] theorem b₀_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    b₀ (T ::ₘ F) = b₀ F + 1 := Multiset.card_cons T F
@[simp] theorem b₀_singleton (T : Nonplanar α) :
    b₀ ({T} : Multiset (Nonplanar α)) = 1 := Multiset.card_singleton T
@[simp] theorem b₀_add (F G : Multiset (Nonplanar α)) :
    b₀ (F + G) = b₀ F + b₀ G := Multiset.card_add F G

/-- The total non-root vertex count of a forest. -/
def alpha (F : Multiset (Nonplanar α)) : ℕ := (F.map Nonplanar.accCount).sum

@[simp] theorem alpha_zero : alpha (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem alpha_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    alpha (T ::ₘ F) = T.accCount + alpha F := by
  simp only [alpha, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alpha_singleton (T : Nonplanar α) :
    alpha ({T} : Multiset (Nonplanar α)) = T.accCount := by
  simp only [alpha, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alpha_add (F G : Multiset (Nonplanar α)) :
    alpha (F + G) = alpha F + alpha G := by
  simp only [alpha, Multiset.map_add, Multiset.sum_add]

/-- `b₀ + alpha`: the total vertex count of a forest (`sigma_eq_sum_numNodes`). -/
def sigma (F : Multiset (Nonplanar α)) : ℕ := b₀ F + alpha F

@[simp] theorem sigma_zero : sigma (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem sigma_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    sigma (T ::ₘ F) = T.numNodes + sigma F := by
  simp only [sigma, b₀_cons, alpha_cons, ← Nonplanar.accCount_add_one]
  omega
@[simp] theorem sigma_singleton (T : Nonplanar α) :
    sigma ({T} : Multiset (Nonplanar α)) = T.numNodes := by
  simp only [sigma, b₀_singleton, alpha_singleton, ← Nonplanar.accCount_add_one]
  omega
@[simp] theorem sigma_add (F G : Multiset (Nonplanar α)) :
    sigma (F + G) = sigma F + sigma G := by
  simp only [sigma, b₀_add, alpha_add]; omega

/-- `sigma` is the total vertex count: the forest case of `#V = b₀ + #E`. -/
theorem sigma_eq_sum_numNodes (F : Multiset (Nonplanar α)) :
    sigma F = (F.map Nonplanar.numNodes).sum := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih => rw [sigma_cons, ih, Multiset.map_cons, Multiset.sum_cons]

end Forest

end RootedTree
