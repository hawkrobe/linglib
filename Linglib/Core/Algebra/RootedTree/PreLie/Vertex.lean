/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Planar
import Mathlib.Data.List.Basic

set_option autoImplicit false

/-!
# Vertex machinery for `Planar α` — `Vertex`, `insertAt`, `vertices`
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}

Per-vertex bookkeeping for planar rooted trees:

- **`Vertex T`** / **`VertexList cs`** — mutual indexed inductives
  enumerating vertices of a tree / a children list.
- **`insertAt v T₂`** — graft `T₂` as a new first child at vertex `v`.
- **`vertices T`** — list of all vertices of `T` in DFS root-first
  order; length = `T.weight`.

These are the foundational vertex operations. The pre-Lie product
`insertSum` (sum over `vertices T₁` of single-vertex grafts) and the
multi-tree multi-vertex `insertion` operator (Foissy 2021 Thm 5.1) are
both downstream consumers in sibling files.

## File scope

- §1: `Vertex`, `VertexList` mutual inductives + `rootVertex`.
- §2: `insertAt`, `insertAtList` mutual recursive defs + simp lemmas.
- §3: `vertices`, `verticesList` enumeration + simp lemmas + length
  consistency (`length_vertices_eq_weight`).

Sibling files:
- `InsertSum.lean` — single-tree pre-Lie product (planar + nonplanar
  descent) using this vertex machinery.
- `Insertion.lean` — multi-tree multi-vertex grafting (Foissy 2021).
- `VertexBijection.lean` — vertex classification + commutativity
  (extends this file's `insertAt`).
- `Algebra.lean` — `RightPreLieAlgebra ℤ` instance.

## Status

`[UPSTREAM]` candidate. Sorry-free, no `noncomputable`.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ## §1: `Vertex` / `VertexList` mutual inductives -/

mutual
/-- A vertex of a planar rooted tree, indexed by the tree it sits in.
    Two constructors:
    - `root` — the root vertex
    - `inChild` — a vertex inside one of the children -/
inductive Vertex : Planar α → Type _
  | root (a : α) (cs : List (Planar α)) : Vertex (Planar.node a cs)
  | inChild (a : α) (cs : List (Planar α)) (v : VertexList cs) :
      Vertex (Planar.node a cs)
/-- A vertex inside one of the entries of a children list, indexed by
    the list. Two constructors:
    - `head` — a vertex inside the head entry
    - `tail` — a vertex inside one of the tail entries -/
inductive VertexList : List (Planar α) → Type _
  | head (c : Planar α) (cs : List (Planar α)) (v : Vertex c) :
      VertexList (c :: cs)
  | tail (c : Planar α) (cs : List (Planar α)) (v : VertexList cs) :
      VertexList (c :: cs)
end

/-- The root vertex of a planar tree. Every `Planar α` has the form
    `Planar.node a cs`, with root `Vertex.root a cs`. -/
def rootVertex : (T : Planar α) → Vertex T
  | .node a cs => .root a cs

@[simp] theorem rootVertex_node (a : α) (cs : List (Planar α)) :
    rootVertex (Planar.node a cs) = Vertex.root a cs := rfl

/-! ## §2: `insertAt` — single-vertex grafting -/

mutual
/-- Insert `T₂` as a new child at the vertex `v` of some tree. The
    resulting tree's shape: `T₂` is prepended to the children list of
    the vertex `v`. -/
def insertAt : ∀ {T : Planar α}, Vertex T → Planar α → Planar α
  | _, Vertex.root a cs,        T₂ => Planar.node a (T₂ :: cs)
  | _, Vertex.inChild a cs vl,  T₂ => Planar.node a (insertAtList vl T₂)
/-- Insert `T₂` at a vertex inside a children list. Same idea as
    `insertAt`, lifted through the list constructor. -/
def insertAtList : ∀ {cs : List (Planar α)}, VertexList cs → Planar α →
    List (Planar α)
  | _, VertexList.head c cs v,  T₂ => insertAt v T₂ :: cs
  | _, VertexList.tail c cs vl, T₂ => c :: insertAtList vl T₂
end

@[simp] theorem insertAt_root (a : α) (cs : List (Planar α)) (T₂ : Planar α) :
    insertAt (Vertex.root a cs) T₂ = Planar.node a (T₂ :: cs) := rfl

@[simp] theorem insertAt_inChild (a : α) (cs : List (Planar α))
    (vl : VertexList cs) (T₂ : Planar α) :
    insertAt (Vertex.inChild a cs vl) T₂ =
      Planar.node a (insertAtList vl T₂) := rfl

@[simp] theorem insertAtList_head (c : Planar α) (cs : List (Planar α))
    (v : Vertex c) (T₂ : Planar α) :
    insertAtList (VertexList.head c cs v) T₂ = insertAt v T₂ :: cs := rfl

@[simp] theorem insertAtList_tail (c : Planar α) (cs : List (Planar α))
    (vl : VertexList cs) (T₂ : Planar α) :
    insertAtList (VertexList.tail c cs vl) T₂ = c :: insertAtList vl T₂ := rfl

/-! ## §3: Vertex enumeration

`vertices T : List (Vertex T)` lists the vertices of `T` in a fixed
order: root first, then a depth-first traversal of children (children
of the head subtree first, then siblings). The length equals
`T.weight`. -/

mutual
/-- All vertices of a planar tree, in root-first order. -/
def vertices : (T : Planar α) → List (Vertex T)
  | .node a cs =>
      Vertex.root a cs ::
        (verticesList cs).map (Vertex.inChild a cs)
/-- All vertex-positions inside a children list, in head-first order. -/
def verticesList : (cs : List (Planar α)) → List (VertexList cs)
  | [] => []
  | c :: cs =>
      (vertices c).map (VertexList.head c cs) ++
        (verticesList cs).map (VertexList.tail c cs)
end

@[simp] theorem vertices_node (a : α) (cs : List (Planar α)) :
    vertices (Planar.node a cs) =
      Vertex.root a cs ::
        (verticesList cs).map (Vertex.inChild a cs) := rfl

@[simp] theorem verticesList_nil :
    verticesList ([] : List (Planar α)) = [] := rfl

@[simp] theorem verticesList_cons (c : Planar α) (cs : List (Planar α)) :
    verticesList (c :: cs) =
      (vertices c).map (VertexList.head c cs) ++
        (verticesList cs).map (VertexList.tail c cs) := rfl

/-! ### Vertex-count consistency

The two countings agree: `(vertices T).length = T.weight`. -/

mutual
theorem length_vertices_eq_weight : ∀ (T : Planar α),
    (vertices T).length = T.weight
  | .node a cs => by
    rw [vertices_node]
    simp only [List.length_cons, List.length_map]
    rw [length_verticesList_eq_weightList cs]
    show weightList cs + 1 = (Planar.node a cs).weight
    show weightList cs + 1 = 1 + weightList cs
    omega
theorem length_verticesList_eq_weightList : ∀ (cs : List (Planar α)),
    (verticesList cs).length = weightList cs
  | [] => rfl
  | c :: cs => by
    rw [verticesList_cons]
    simp only [List.length_append, List.length_map]
    rw [length_vertices_eq_weight c, length_verticesList_eq_weightList cs]
    show c.weight + weightList cs = weightList (c :: cs)
    rfl
end

end Planar

end RootedTree
