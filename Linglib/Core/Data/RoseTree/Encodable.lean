/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Basic
import Linglib.Core.Data.Tree.Encodable

/-!
# Forests are binary trees

A forest, a list of rose trees, is either empty or a first tree followed by a forest, and the
first tree is a value over the forest of its children. A binary tree is either `nil` or a value
with a left and a right subtree. Reading the left subtree as the children of the first tree and
the right subtree as the rest of the forest identifies the two: this is the natural
correspondence between forests and binary trees of [knuth-1997], the left-child right-sibling
representation. A rose tree is a value together with the forest of its children, hence a value
together with a binary tree, and rose trees over an encodable type are encodable.

## Main declarations

* `BinaryTree.ofForest`, `BinaryTree.toForest`: the natural correspondence and its inverse,
  bundled as `BinaryTree.equivForest`; `BinaryTree.cons` is the list cons transported along it.
* `RoseTree.equivProdBinaryTree`: a rose tree is a value together with a binary tree.
* `RoseTree.encodable`, `RoseTree.countable`: the instances transported along it.

## Main results

* `BinaryTree.numNodes_ofForest`, `BinaryTree.numNodes_cons`: the correspondence preserves the
  number of nodes.
-/

namespace BinaryTree

variable {α : Type*}

mutual

/-- The natural correspondence: a forest becomes the binary tree obtained by `cons`ing its
trees, in order, onto `nil`. -/
def ofForest : List (RoseTree α) → BinaryTree α
  | [] => nil
  | t :: rest => cons t (ofForest rest)

/-- The list `cons` transported along the natural correspondence: a tree becomes a node whose
left subtree is the forest of its children and whose right subtree is the rest of the forest. -/
def cons : RoseTree α → BinaryTree α → BinaryTree α
  | .node a cs, r => node a (ofForest cs) r

end

/-- The inverse of the natural correspondence `BinaryTree.ofForest`. -/
def toForest : BinaryTree α → List (RoseTree α)
  | nil => []
  | node a l r => RoseTree.node a (toForest l) :: toForest r

@[simp] theorem ofForest_nil : ofForest ([] : List (RoseTree α)) = nil := rfl

@[simp] theorem ofForest_cons (t : RoseTree α) (rest : List (RoseTree α)) :
    ofForest (t :: rest) = cons t (ofForest rest) := rfl

@[simp] theorem cons_node (a : α) (cs : List (RoseTree α)) (r : BinaryTree α) :
    cons (RoseTree.node a cs) r = node a (ofForest cs) r := rfl

@[simp] theorem toForest_nil : toForest (nil : BinaryTree α) = [] := rfl

@[simp] theorem toForest_node (a : α) (l r : BinaryTree α) :
    toForest (node a l r) = RoseTree.node a (toForest l) :: toForest r := rfl

mutual

@[simp] theorem toForest_ofForest : ∀ cs : List (RoseTree α), toForest (ofForest cs) = cs
  | [] => rfl
  | t :: rest => by rw [ofForest_cons, toForest_cons, toForest_ofForest rest]

@[simp] theorem toForest_cons : ∀ (t : RoseTree α) (r : BinaryTree α),
    toForest (cons t r) = t :: toForest r
  | .node a cs, r => by rw [cons_node, toForest_node, toForest_ofForest cs]

end

@[simp] theorem ofForest_toForest (t : BinaryTree α) : ofForest (toForest t) = t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => rw [toForest_node, ofForest_cons, cons_node, hl, hr]

/-- The natural correspondence between binary trees and forests. -/
@[simps] def equivForest : BinaryTree α ≃ List (RoseTree α) :=
  ⟨toForest, ofForest, ofForest_toForest, toForest_ofForest⟩

mutual

theorem numNodes_ofForest :
    ∀ cs : List (RoseTree α), (ofForest cs).numNodes = (cs.map RoseTree.numNodes).sum
  | [] => rfl
  | t :: rest => by
    rw [ofForest_cons, numNodes_cons, numNodes_ofForest rest, List.map_cons, List.sum_cons]

theorem numNodes_cons : ∀ (t : RoseTree α) (r : BinaryTree α),
    (cons t r).numNodes = t.numNodes + r.numNodes
  | .node a cs, r => by
    rw [cons_node, numNodes, numNodes_ofForest cs, RoseTree.numNodes_node]; omega

end

end BinaryTree

namespace RoseTree

variable {α : Type*}

/-- A rose tree is its root value together with the binary tree of the forest of its children. -/
@[simps] def equivProdBinaryTree : RoseTree α ≃ α × BinaryTree α where
  toFun t := (t.value, .ofForest t.children)
  invFun p := node p.1 p.2.toForest
  left_inv t := by cases t; simp
  right_inv p := by simp

instance encodable [Encodable α] : Encodable (RoseTree α) := .ofEquiv _ equivProdBinaryTree

instance countable [Countable α] : Countable (RoseTree α) := by
  have := Encodable.ofCountable α
  infer_instance

end RoseTree
