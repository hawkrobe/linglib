import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Defs
import Linglib.Core.Order.Branching

set_option autoImplicit false

/-!
# Planar n-ary rooted trees with vertex labels in `α`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

A **planar rooted tree** has: a distinguished root vertex, an
α-label at every vertex, and an ordered (list-valued) sequence of
children at each non-leaf vertex. Each vertex's "arity" is the length
of its child list; leaves are vertices with empty child lists. There is
no global arity bound — vertices may have any number of children.

This is the most general planar tree carrier the Connes-Kreimer-style
Hopf algebra needs. Specializations as subtypes:

- `Binary` (every internal vertex has exactly 2 children) ≃ `FreeMagma α`
  (the existing linglib binary planar carrier).
- `NaryAtMost n` (every vertex has ≤ n children).
- `NaryExactly n` (every internal vertex has exactly n children, leaves 0).

The nonplanar version (children as multiset, not list) is in
`RootedTree.Nonplanar` (sibling file), defined as a quotient by
permutations of children at each level.

## Why list-of-children, not multiset directly

Lean 4's strict positivity check rejects
`inductive Tree | node : α → Multiset (Tree α) → Tree α` because
`Multiset = Quot (List _) _` is opaque to the positivity checker. The
standard workaround: define the planar (list-valued) version as a
genuine inductive, then quotient by a permutation relation to get the
nonplanar version. This file provides the list-valued primitive;
`Nonplanar.lean` provides the quotient.

## MCB anchor

[marcolli-chomsky-berwick-2025] §1.11 introduces n-ary syntactic
objects `SO^(n) ≃ ℑ^(n)_{SO_0}` as the free nonassociative commutative
n-magma; book p. 96 Definition 1.11.2. §1.17 uses the n-ary
Connes-Kreimer Hopf algebra of rooted trees in the recursive
construction of solutions to combinatorial Dyson-Schwinger equations
(book p. 149-150). The carrier here is parameterized over arity (no
fixed n), subsuming all n-ary cases via subtypes.

[foissy-introduction-hopf-algebras-trees] §1.1 (p. 3) introduces
rooted trees as finite graphs, connected and without cycles, with a
distinguished root vertex; this file's `Planar` is the planar / ordered
variant (Foissy's H_PR setting, §2). The nonplanar variant (Foissy's
H_R, §1) is the quotient in `Nonplanar.lean`.

## Status

`[UPSTREAM]` candidate; future home something like
`Mathlib.Combinatorics.RootedTree.Planar`. No sorries, no
`noncomputable`, no `decide` in this file.
-/

namespace RootedTree

/-! ## §1: The `Planar` inductive

A planar rooted tree is built by `node a cs` where `a : α` is the root
label and `cs : List (Planar α)` is the ordered list of children.
Leaves are `node a []`. -/

/-- A planar rooted tree with α-labeled vertices and ordered children. -/
inductive Planar (α : Type*) : Type _
  | node (a : α) (cs : List (Planar α)) : Planar α

namespace Planar

variable {α : Type*}

/-! ## §2: Basic projections -/

/-- The label at the root vertex. -/
def label : Planar α → α
  | .node a _ => a

/-- The (ordered) list of children at the root. -/
def children : Planar α → List (Planar α)
  | .node _ cs => cs

@[simp] theorem label_node (a : α) (cs : List (Planar α)) :
    Planar.label (Planar.node a cs) = a := rfl

@[simp] theorem children_node (a : α) (cs : List (Planar α)) :
    Planar.children (Planar.node a cs) = cs := rfl

/-! ## §3: Counting — weight, arity, depth

Defined by structural recursion (mutual with the list-of-trees aux). -/

mutual
/-- The **weight** of a tree: total number of vertices. -/
def weight : Planar α → Nat
  | .node _ cs => 1 + weightList cs
/-- Auxiliary: total weight of a list of trees. -/
def weightList : List (Planar α) → Nat
  | [] => 0
  | t :: ts => weight t + weightList ts
end

mutual
/-- The **depth** of a tree: longest root-to-leaf path length (in
    edges). A leaf has depth 0. -/
def depth : Planar α → Nat
  | .node _ cs => 1 + depthMaxList cs
/-- Auxiliary: max depth across a list of trees (0 for empty). -/
def depthMaxList : List (Planar α) → Nat
  | [] => 0
  | t :: ts => max (depth t) (depthMaxList ts)
end

/-- The **arity** of the root vertex: number of children. Leaves have
    arity 0. -/
def arity : Planar α → Nat
  | .node _ cs => cs.length

/-- A tree is a **leaf** if its root has no children. -/
def isLeaf : Planar α → Bool
  | .node _ [] => true
  | .node _ (_ :: _) => false

@[simp] theorem arity_node (a : α) (cs : List (Planar α)) :
    Planar.arity (Planar.node a cs) = cs.length := rfl

@[simp] theorem isLeaf_node_nil (a : α) :
    Planar.isLeaf (Planar.node a [] : Planar α) = true := rfl

@[simp] theorem isLeaf_node_cons (a : α) (c : Planar α) (cs : List (Planar α)) :
    Planar.isLeaf (Planar.node a (c :: cs)) = false := rfl

/-! ## §4: Smart constructors -/

/-- A **leaf** with the given α-label. -/
def leaf (a : α) : Planar α := .node a []

/-- A **unary** node: single child. -/
def unary (a : α) (c : Planar α) : Planar α := .node a [c]

/-- A **binary** node: two children, in left-to-right order. -/
def binary (a : α) (l r : Planar α) : Planar α := .node a [l, r]

/-- An **n-ary** node: list of children. -/
def nary (a : α) (cs : List (Planar α)) : Planar α := .node a cs

@[simp] theorem leaf_def (a : α) : leaf a = (Planar.node a [] : Planar α) := rfl
@[simp] theorem unary_def (a : α) (c : Planar α) :
    unary a c = .node a [c] := rfl
@[simp] theorem binary_def (a : α) (l r : Planar α) :
    binary a l r = .node a [l, r] := rfl
@[simp] theorem nary_def (a : α) (cs : List (Planar α)) :
    nary a cs = .node a cs := rfl

/-! ## §5: Functoriality

`Planar` is a functor in the vertex-label parameter: a function `f : α → β`
lifts to `Planar α → Planar β` by relabeling every vertex. Defined by
mutual structural recursion on `(tree, list-of-trees)`. Counterpart
of mathlib's `Tree.map` for binary trees and `List.map` for lists. -/

mutual
/-- Map a function over the vertex labels of a planar rooted tree. -/
def map {β : Type*} (f : α → β) : Planar α → Planar β
  | .node a cs => .node (f a) (mapList f cs)
/-- Auxiliary: map across a list of children. -/
def mapList {β : Type*} (f : α → β) : List (Planar α) → List (Planar β)
  | [] => []
  | c :: cs => map f c :: mapList f cs
end

@[simp] theorem map_node {β : Type*} (f : α → β) (a : α) (cs : List (Planar α)) :
    map f (Planar.node a cs) = .node (f a) (mapList f cs) := rfl

@[simp] theorem mapList_nil {β : Type*} (f : α → β) :
    mapList f ([] : List (Planar α)) = [] := rfl

@[simp] theorem mapList_cons {β : Type*} (f : α → β)
    (c : Planar α) (cs : List (Planar α)) :
    mapList f (c :: cs) = map f c :: mapList f cs := rfl

/-- `mapList f` agrees with `List.map (map f)`. Bridge to mathlib's
    `List.map` API. -/
theorem mapList_eq_listMap {β : Type*} (f : α → β) (cs : List (Planar α)) :
    mapList f cs = cs.map (map f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [mapList_cons, List.map_cons, ih]

/-- `map` on a leaf. Provable by `simp` from `leaf_def + map_node + mapList_nil`,
    so kept as a plain `rw` lemma (no `@[simp]`) to avoid simp non-confluence. -/
theorem map_leaf {β : Type*} (f : α → β) (a : α) :
    map f (leaf a) = leaf (f a) := rfl

mutual
/-- Functoriality: `map id = id`. -/
@[simp] theorem map_id : ∀ (t : Planar α), map id t = t
  | .node a cs => by rw [map_node, mapList_id]; rfl
@[simp] theorem mapList_id : ∀ (cs : List (Planar α)), mapList id cs = cs
  | [] => rfl
  | c :: cs => by rw [mapList_cons, map_id, mapList_id]
end

mutual
/-- Functoriality: `map (g ∘ f) = map g ∘ map f`. -/
@[simp] theorem map_map {β γ : Type*} (f : α → β) (g : β → γ) :
    ∀ (t : Planar α), map g (map f t) = map (g ∘ f) t
  | .node a cs => by rw [map_node, map_node, map_node, mapList_mapList]; rfl
@[simp] theorem mapList_mapList {β γ : Type*} (f : α → β) (g : β → γ) :
    ∀ (cs : List (Planar α)), mapList g (mapList f cs) = mapList (g ∘ f) cs
  | [] => rfl
  | c :: cs => by
    rw [mapList_cons, mapList_cons, mapList_cons, map_map, mapList_mapList]
end

/-! ### Counting interactions -/

mutual
@[simp] theorem weight_map {β : Type*} (f : α → β) :
    ∀ (t : Planar α), (map f t).weight = t.weight
  | .node a cs => by
    rw [map_node]
    show 1 + weightList (mapList f cs) = 1 + weightList cs
    rw [weightList_mapList f cs]
theorem weightList_mapList {β : Type*} (f : α → β) :
    ∀ (cs : List (Planar α)), weightList (mapList f cs) = weightList cs
  | [] => by rfl
  | c :: cs => by
    rw [mapList_cons]
    show weight (map f c) + weightList (mapList f cs)
       = weight c + weightList cs
    rw [weight_map f c, weightList_mapList f cs]
end

mutual
@[simp] theorem depth_map {β : Type*} (f : α → β) :
    ∀ (t : Planar α), (map f t).depth = t.depth
  | .node a cs => by
    rw [map_node]
    show 1 + depthMaxList (mapList f cs) = 1 + depthMaxList cs
    rw [depthMaxList_mapList f cs]
theorem depthMaxList_mapList {β : Type*} (f : α → β) :
    ∀ (cs : List (Planar α)), depthMaxList (mapList f cs) = depthMaxList cs
  | [] => by rfl
  | c :: cs => by
    rw [mapList_cons]
    show max (depth (map f c)) (depthMaxList (mapList f cs))
       = max (depth c) (depthMaxList cs)
    rw [depth_map f c, depthMaxList_mapList f cs]
end

@[simp] theorem arity_map {β : Type*} (f : α → β) (t : Planar α) :
    (map f t).arity = t.arity := by
  cases t with
  | node a cs =>
    rw [map_node]
    show (mapList f cs).length = cs.length
    rw [mapList_eq_listMap, List.length_map]

@[simp] theorem isLeaf_map {β : Type*} (f : α → β) (t : Planar α) :
    (map f t).isLeaf = t.isLeaf := by
  cases t with
  | node a cs =>
    cases cs with
    | nil => rfl
    | cons _ _ => rfl

/-! ## §5b: Sanity tests at compile time -/

example : Planar.weight (leaf 1 : Planar Nat) = 1 := by
  unfold leaf weight weightList; rfl
example : Planar.arity (leaf 1 : Planar Nat) = 0 := rfl
example : Planar.depth (leaf 1 : Planar Nat) = 1 := by
  unfold leaf depth depthMaxList; rfl
example : Planar.isLeaf (leaf 1 : Planar Nat) = true := rfl

example : Planar.weight (binary 1 (leaf 2) (leaf 3) : Planar Nat) = 3 := by
  unfold binary leaf weight weightList; rfl
example : Planar.arity (binary 1 (leaf 2) (leaf 3) : Planar Nat) = 2 := rfl
example : Planar.depth (binary 1 (leaf 2) (leaf 3) : Planar Nat) = 2 := by
  unfold binary leaf depth depthMaxList; rfl

/-! ## §6: Inhabited -/

instance [Inhabited α] : Inhabited (Planar α) :=
  ⟨leaf default⟩

end Planar

end RootedTree

/-! ### Rose-tree interface instances

`Planar` joins the `Core.Order.Branching` tower: Gorn-address
machinery, the dominance order, and the B&P command bridge come
generically from the `children` projection. -/

namespace RootedTree.Planar

instance {α : Type*} : Core.Order.Branching (Planar α) := ⟨Planar.children⟩

@[simp] theorem branching_children {α : Type*} (t : Planar α) :
    Core.Order.Branching.children t = t.children := rfl

noncomputable instance {α : Type*} : Core.Order.FiniteBranching (Planar α) where
  measure := sizeOf
  measure_children {c t} hc := by
    cases t with
    | node a cs =>
      simp only [branching_children, Planar.children] at hc
      have := List.sizeOf_lt_of_mem hc
      simp only [Planar.node.sizeOf_spec]
      omega

end RootedTree.Planar
