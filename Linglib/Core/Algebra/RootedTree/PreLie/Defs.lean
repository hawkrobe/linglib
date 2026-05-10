import Linglib.Core.Combinatorics.RootedTree.Planar
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons

set_option autoImplicit false

/-!
# Pre-Lie product (vertex grafting) on `RootedTree.Planar α` — planar substrate
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}

The **vertex-grafting pre-Lie product** on planar n-ary rooted trees:
for trees `T₁, T₂ : Planar α`, `T₁ ◁ T₂` is the multiset of all trees
obtained by grafting `T₂` as a new child of some vertex of `T₁`:

  T₁ ◁ T₂ = Σ_{v ∈ V(T₁)} graft(v, T₁, T₂)

where `graft(v, T₁, T₂)` walks to the vertex `v` and prepends `T₂` to
its child list. The number of summands equals `weight T₁` (the total
vertex count). For a leaf `node a []`, `T₁ ◁ T₂ = {node a [T₂]}`: a
single grafting at the root.

## Reference

@cite{foissy-typed-decorated-rooted-trees-2018} Proposition 2.2 defines
the multiple pre-Lie product on D-decorated T-typed rooted trees (D =
decoration set, T = edge type set). Specialized to T = {*} (single edge
type) and decoration set α, this is exactly our `Planar.insertSum`.
Foissy's Corollary 2.7 proves it is the FREE pre-Lie algebra on α
generators.

@cite{chapoton-livernet-2001} introduced the original CL pre-Lie
product on undecorated rooted trees, of which the present construction
is the decorated extension.

## Relation to MCB §1.7

@cite{marcolli-chomsky-berwick-2025} Definition 1.7.1 (book p. 77)
defines a DIFFERENT pre-Lie product on **nonplanar BINARY** rooted
trees with leaf labels in `SO_0` (internal vertices unlabeled), via
**edge subdivision**: each insertion adds a new internal valence-2
vertex on the chosen edge of `T₁`, with `T₂` attached as the new
vertex's other child. MCB's product gives `numEdges T₁` summands (zero
on a leaf, since leaves have no edges); the present construction gives
`weight T₁` summands (one on a leaf).

The two are distinct algebras on distinct carriers — neither is a
specialization of the other. Both satisfy the abstract pre-Lie identity
(MCB Lemma 1.7.2 for theirs; Foissy 2018 Prop 2.2 for ours), so the
abstract pre-Lie typeclass machinery (mathlib's `RightPreLieAlgebra`)
applies to both. If a future Studies file directly formalizes MCB
§1.7's binary Insertion Lie Algebra, it would add a separate binary
substrate file with its own `RightPreLieAlgebra` instance.

For the chain (R.3 → R.4 Guin-Oudom → R.5 GL → R.7 Δ^c coassoc by
duality), what is needed is the n-ary fully-decorated pre-Lie. That is
Foissy 2018, not MCB §1.7.

## File scope (R.3a)

This file (`PreLie/Defs.lean`) carries §1-§4 of the planar substrate:
- §1: `Planar.insertSum` (the product itself)
- §2: cardinality (`card_insertSum_eq_weight`)
- §3: per-vertex machinery (`Vertex`, `insertAt`, `vertices`)
- §4: decomposition lemma `insertSum_eq_coe_map_insertAt`

Sibling files in `PreLie/` extend the substrate:
- `EdgeBijection.lean` (R.3b): vertex classification + commutativity
- `Nonplanar.lean` (R.3c): descent through `Nonplanar.mk`
- `Algebra.lean` (R.3d): bilinear extension + pre-Lie identity +
  `RightPreLieAlgebra ℤ` instance.

## Status

`[UPSTREAM]` candidate. Sorry-free.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ## §1: `insertSum` — the vertex-grafting product

Mutually recursive on `(Planar, List Planar)` mirroring `weight` /
`weightList` etc. Each summand of `insertSum T₁ T₂` corresponds to a
choice of vertex `v` in `T₁`; the corresponding tree replaces `v`'s
children list `cs` with `T₂ :: cs`. -/

mutual
/-- The pre-Lie product `T₁ ◁ T₂` on `Planar α` (vertex grafting): the
    multiset of all trees obtained by grafting `T₂` as a new child of
    some vertex of `T₁`. -/
def insertSum : Planar α → Planar α → Multiset (Planar α)
  | .node a cs, T₂ =>
      ((Planar.node a (T₂ :: cs)) : Planar α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs')
/-- Auxiliary: graft `T₂` inside one of the entries of a children list,
    returning the multiset of resulting children-lists (one per vertex
    inside the list). -/
def insertSumList : List (Planar α) → Planar α →
    Multiset (List (Planar α))
  | [], _ => 0
  | c :: cs, T₂ =>
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs')
end

/-- Notation `T₁ ◁ T₂` for `insertSum T₁ T₂`. The right-triangular
    Unicode glyph matches Foissy's typesetting (and the deleted
    `Free/PreLie.lean`'s convention). Scoped to avoid clashing with
    mathlib's `LeftPreLieRing` notation. -/
scoped infixl:65 " ◁ " => insertSum

@[simp] theorem insertSum_node (a : α) (cs : List (Planar α))
    (T₂ : Planar α) :
    (Planar.node a cs) ◁ T₂ =
      ((Planar.node a (T₂ :: cs)) : Planar α) ::ₘ
        (insertSumList cs T₂).map (fun cs' => .node a cs') := by
  unfold insertSum; rfl

@[simp] theorem insertSumList_nil (T₂ : Planar α) :
    insertSumList ([] : List (Planar α)) T₂ = 0 := by
  conv_lhs => unfold insertSumList

@[simp] theorem insertSumList_cons (c : Planar α) (cs : List (Planar α))
    (T₂ : Planar α) :
    insertSumList (c :: cs) T₂ =
      (insertSum c T₂).map (fun c' => c' :: cs)
        + (insertSumList cs T₂).map (fun cs' => c :: cs') := by
  conv_lhs => unfold insertSumList

/-- A leaf has exactly one summand: graft `T₂` at the root. -/
@[simp] theorem insertSum_leaf (a : α) (T₂ : Planar α) :
    Planar.leaf a ◁ T₂ =
      ({Planar.node a [T₂]} : Multiset (Planar α)) := by
  show insertSum (Planar.node a []) T₂ = _
  rw [insertSum_node, insertSumList_nil]
  simp

/-! ## §2: Cardinality — `card (T₁ ◁ T₂) = T₁.weight`

Each vertex of `T₁` contributes one summand. Proved by mutual
structural induction mirroring the definition. -/

mutual
/-- The number of summands in `T₁ ◁ T₂` equals `T₁.weight`
    (total vertex count). -/
theorem card_insertSum_eq_weight : ∀ (T₁ T₂ : Planar α),
    Multiset.card (T₁ ◁ T₂) = T₁.weight
  | .node a cs, T₂ => by
    rw [insertSum_node]
    simp only [Multiset.card_cons, Multiset.card_map]
    rw [card_insertSumList_eq_weightList cs T₂]
    show weightList cs + 1 = (Planar.node a cs).weight
    show weightList cs + 1 = 1 + weightList cs
    omega
/-- The number of children-lists in `insertSumList cs T₂` equals
    `weightList cs` (sum of weights of entries). -/
theorem card_insertSumList_eq_weightList : ∀ (cs : List (Planar α))
    (T₂ : Planar α),
    Multiset.card (insertSumList cs T₂) = weightList cs
  | [], _ => by rw [insertSumList_nil]; rfl
  | c :: cs', T₂ => by
    rw [insertSumList_cons]
    simp only [Multiset.card_add, Multiset.card_map]
    rw [card_insertSum_eq_weight c T₂,
        card_insertSumList_eq_weightList cs' T₂]
    show c.weight + weightList cs' = weightList (c :: cs')
    rfl
end

/-! ## §3: Per-vertex machinery — `Vertex`, `insertAt`, `vertices`

To prove the pre-Lie identity (R.3d) and the descent through
`Nonplanar.mk` (R.3c), per-vertex bookkeeping is needed: which vertex
of `T₁` is being grafted onto. The mutual indexed inductives `Vertex`
and `VertexList` enumerate vertices of a tree and a children-list,
respectively; `insertAt` performs the grafting at a specific vertex;
`vertices` enumerates them all in a fixed order. The decomposition
lemma in §4 then bridges `insertSum` to the per-vertex view. -/

mutual
/-- A vertex of a planar rooted tree, indexed by the tree it sits in.
    Two constructors:
    - `root` — the root vertex
    - `inChild` — a vertex inside one of the children
-/
inductive Vertex : Planar α → Type _
  | root (a : α) (cs : List (Planar α)) : Vertex (Planar.node a cs)
  | inChild (a : α) (cs : List (Planar α)) (v : VertexList cs) :
      Vertex (Planar.node a cs)
/-- A vertex inside one of the entries of a children list, indexed by
    the list. Two constructors:
    - `head` — a vertex inside the head entry
    - `tail` — a vertex inside one of the tail entries
-/
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

/-! ### Vertex enumeration

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

/-! ## §4: Decomposition — `insertSum` via `vertices` + `insertAt`

Bridge lemma between the recursive (Multiset) formulation of `insertSum`
in §1 and the per-vertex (List) formulation in §3. The lemma is the
basis for the pre-Lie identity proof in R.3d: each summand of
`insertSum T₁ T₂` is uniquely identified by a vertex of `T₁`. -/

mutual
/-- **Decomposition lemma**: `T₁ ◁ T₂` equals the multiset of
    `insertAt v T₂` for `v` ranging over `vertices T₁`. -/
theorem insertSum_eq_coe_map_insertAt : ∀ (T₁ T₂ : Planar α),
    T₁ ◁ T₂ =
      ((vertices T₁).map (fun v => insertAt v T₂) : Multiset (Planar α))
  | .node a cs, T₂ => by
    rw [insertSum_node, vertices_node,
        insertSumList_eq_coe_map_insertAtList cs T₂]
    -- Rewrite both sides to a normal form on `List` then compare via Multiset.
    simp only [Multiset.map_coe, List.map_cons, List.map_map,
               Function.comp_def, insertAt_root, insertAt_inChild,
               ← Multiset.cons_coe]
/-- `insertSumList cs T₂` equals the multiset of `insertAtList vl T₂`
    for `vl` ranging over `verticesList cs`. -/
theorem insertSumList_eq_coe_map_insertAtList :
    ∀ (cs : List (Planar α)) (T₂ : Planar α),
    insertSumList cs T₂ =
      ((verticesList cs).map (fun vl => insertAtList vl T₂)
          : Multiset (List (Planar α)))
  | [], _ => by
    rw [insertSumList_nil, verticesList_nil]
    rfl
  | c :: cs, T₂ => by
    rw [insertSumList_cons, verticesList_cons,
        insertSum_eq_coe_map_insertAt c T₂,
        insertSumList_eq_coe_map_insertAtList cs T₂]
    simp only [Multiset.map_coe, List.map_append, List.map_map,
               Function.comp_def, insertAtList_head, insertAtList_tail,
               ← Multiset.coe_add]
end

/-! ### Cardinality consistency

The two cardinality computations agree: `(T₁ ◁ T₂).card = (vertices T₁).length`. -/

theorem card_insertSum_eq_length_vertices (T₁ T₂ : Planar α) :
    Multiset.card (T₁ ◁ T₂) = (vertices T₁).length := by
  rw [card_insertSum_eq_weight, length_vertices_eq_weight]

/-! ## §5: Sanity tests at compile time -/

section Tests

example : (Planar.leaf 1 : Planar Nat) ◁ Planar.leaf 2
    = ({Planar.node 1 [Planar.leaf 2]} : Multiset (Planar Nat)) := by
  rw [insertSum_leaf]

/-- A binary tree has 3 vertices, hence 3 grafting summands. -/
example : Multiset.card
    ((Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3) : Planar Nat) ◁
      Planar.leaf 4) = 3 := by
  rw [card_insertSum_eq_weight]
  show (Planar.binary 1 (Planar.leaf 2) (Planar.leaf 3) : Planar Nat).weight = 3
  unfold Planar.binary Planar.leaf weight weightList; rfl

/-- The grafting decomposition: each summand corresponds to a vertex. -/
example (T₁ T₂ : Planar Nat) :
    Multiset.card (T₁ ◁ T₂) = (vertices T₁).length :=
  card_insertSum_eq_length_vertices T₁ T₂

end Tests

end Planar

end RootedTree
