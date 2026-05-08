import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

universe u v

/-!
# Planar n-ary rooted trees with vertex labels in `α`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

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

@cite{marcolli-chomsky-berwick-2025} §1.11 introduces n-ary syntactic
objects `SO^(n) ≃ ℑ^(n)_{SO_0}` as the free nonassociative commutative
n-magma; book p. 96 Definition 1.11.2. §1.17 uses the n-ary
Connes-Kreimer Hopf algebra of rooted trees in the recursive
construction of solutions to combinatorial Dyson-Schwinger equations
(book p. 149-150). The carrier here is parameterized over arity (no
fixed n), subsuming all n-ary cases via subtypes.

@cite{foissy-introduction-hopf-algebras-trees} §1.1 (p. 3) introduces
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
inductive Planar (α : Type u) : Type u
  | node (a : α) (cs : List (Planar α)) : Planar α

namespace Planar

variable {α : Type u}

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

/-! ## §5: Sanity tests at compile time -/

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
