import Linglib.Core.Data.RoseTree.Basic

set_option autoImplicit false

/-!
# Admissible cuts on n-ary rooted trees
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

An **admissible cut** of a tree T is a subset of edges such that every
root-to-leaf path of T contains at most one selected edge. After
deleting the selected edges, T decomposes into:

- The *cut forest* `cutForest c`: the multiset of subtrees that get
  separated from the root after the deletion.
- The *remainder*: the connected component containing the root, which
  comes in two flavors:
  - **`remainderDeletion`** ≈ MCB's `T/^p` (admissible cut, Definition 1.2.6,
    book p. 31): just remove the cut subtrees; the parent vertex now has
    fewer children, so the remainder lives in the *at-most-n-ary* substrate
    (Lemma 1.2.11, book p. 38). NOT MCB's `T/^d` (Definition 1.2.5),
    which would re-binarize via edge contraction.
  - **`remainderTrace`** ≈ MCB's `T/^c` (contraction, Definition 1.2.4,
    book p. 30; requires `[Inhabited α]`): replace each cut subtree with
    a single trace-leaf labeled `default`; the parent's arity is preserved.
    Used at the C-I (semantic) interface for FormCopy.

This file provides admissible cuts on the n-ary rooted-tree carrier
`RoseTree α` (`RoseTree/Basic.lean`). The cuts work uniformly across arities —
the binary case inherits as a subtype.

## Status

`[UPSTREAM]` candidate. No sorries.

## MCB anchor

[marcolli-chomsky-berwick-2025] Definition 1.2.6 (book p. 31) for
the admissible cut definition; Lemma 1.2.7 (book p. 32) for the
equivalence with forest extraction. Definitions 1.2.4 (T/^c, p. 30),
1.2.5 (T/^d, p. 31), 1.2.6 (T/^p, p. 31) for the three remainder
flavors. We expose `remainderDeletion` (T/^p, p. 31) and
`remainderTrace` (T/^c, p. 30); MCB's T/^d (deletion-then-rebinarize)
is not directly exposed here since it's the closest to the consumer-
visible "Externalization" form (PF interface) and can be derived from
T/^p via tree-binarization at the algebra layer.
-/

namespace RoseTree

variable {α : Type*}

/-! ## §1: The `Cut` inductive

A cut is recursively built from a per-vertex choice: at the root, for
each child edge, decide whether to (a) cut this edge (extracting that
subtree), or (b) recurse into that subtree's own cut. The "antichain"
condition (no two cuts on the same root-to-leaf path) is baked in
because once you cut an edge, you don't recurse beneath it. -/

mutual
/-- An admissible cut on a tree T: at the root vertex, a per-child
    cut decision for each child. (For a leaf, the empty list of
    children gives the unique trivial cut.) -/
inductive Cut : RoseTree α → Type _
  /-- A cut on a tree, given as a per-child decision list (matching
      the children list of the root by length). -/
  | mk {a : α} {cs : List (RoseTree α)} (decisions : ChildCutList cs) : Cut (.node a cs)
/-- A per-child cut decision: either `extract` (cut the edge and
    extract this subtree whole) or `recurse cut` (keep this edge,
    apply `cut` to the subtree). -/
inductive ChildCut : RoseTree α → Type _
  /-- Extract this subtree whole. -/
  | extract (t : RoseTree α) : ChildCut t
  /-- Don't cut at this edge; recurse into the subtree. -/
  | recurse {t : RoseTree α} (c : Cut t) : ChildCut t
/-- A list of `ChildCut` decisions, indexed by the children list. -/
inductive ChildCutList : List (RoseTree α) → Type _
  | nil : ChildCutList []
  | cons {t : RoseTree α} {ts : List (RoseTree α)} (d : ChildCut t) (ds : ChildCutList ts) :
      ChildCutList (t :: ts)
end

/-! ## §2: The empty cut

For every tree, there is a canonical "empty cut" that recurses everywhere
and extracts nothing. -/

mutual
/-- The empty cut on a tree: recurse into every child with the empty
    cut, never extract. -/
def emptyCut : (t : RoseTree α) → Cut t
  | .node _ cs => .mk (emptyCutList cs)
/-- The all-recurse decision list for a list of children. -/
def emptyCutList : (cs : List (RoseTree α)) → ChildCutList cs
  | [] => .nil
  | t :: ts => .cons (.recurse (emptyCut t)) (emptyCutList ts)
end

/-- The total cut: extract every child whole at the root level. (Note:
    this is shallow — it doesn't recurse. The "total cut" in Foissy's
    sense extracting the whole tree as a single piece is not directly
    representable in this Cut type; it lives at the bialgebra layer
    via the explicit `T ⊗ 1` term.) -/
def shallowTotalCut (t : RoseTree α) : Cut t :=
  match t with
  | .node _ cs =>
    let rec go : (cs : List (RoseTree α)) → ChildCutList cs
      | [] => .nil
      | t :: ts => .cons (.extract t) (go ts)
    .mk (go cs)

/-! ## §3: The cut forest

For a cut `c : Cut T`, `cutForest c` is the multiset of subtrees
extracted by `c`. We use `List` for now (the multiset structure
emerges at the Hopf algebra layer via `Multiset.ofList`). -/

mutual
/-- The list of subtrees extracted by a cut. -/
def cutForest : {t : RoseTree α} → Cut t → List (RoseTree α)
  | _, .mk decisions => cutForestList decisions
/-- Auxiliary: extracted subtrees from a child-decision list. -/
def cutForestList : {cs : List (RoseTree α)} → ChildCutList cs → List (RoseTree α)
  | _, .nil => []
  | _, .cons d ds => cutForestChild d ++ cutForestList ds
/-- Auxiliary: extracted subtrees from a single child-decision. -/
def cutForestChild : {t : RoseTree α} → ChildCut t → List (RoseTree α)
  | _, .extract t => [t]
  | _, .recurse c => cutForest c
end

/-! ## §4: Remainders

Two remainder flavors per MCB §1.11.6:

- `remainderDeletion c` (T/^p): subtree replaced by *nothing*
  (parent loses a child). Arity of remainder vertices may decrease.
- `remainderTrace c` (T/^c, with `[Inhabited α]`): subtree replaced by
  a trace-leaf labeled `default`. Arity is preserved everywhere.
-/

mutual
/-- Deletion remainder T/^p: cut subtrees disappear; parent loses children. -/
def remainderDeletion : {t : RoseTree α} → Cut t → RoseTree α
  | .node a _, .mk decisions => .node a (remainderDeletionList decisions)
/-- Auxiliary: deletion remainder for a child-decision list — extracted
    children disappear from the list. -/
def remainderDeletionList : {cs : List (RoseTree α)} → ChildCutList cs → List (RoseTree α)
  | _, .nil => []
  | _, .cons d ds =>
    match d with
    | .extract _ => remainderDeletionList ds        -- this child gone
    | .recurse c => remainderDeletion c :: remainderDeletionList ds
end

mutual
/-- Trace remainder T/^c: cut subtrees replaced with `default`-leaves.
    Arity of all vertices preserved. -/
def remainderTrace [Inhabited α] : {t : RoseTree α} → Cut t → RoseTree α
  | .node a _, .mk decisions => .node a (remainderTraceList decisions)
/-- Auxiliary: trace remainder for a child-decision list. -/
def remainderTraceList [Inhabited α] :
    {cs : List (RoseTree α)} → ChildCutList cs → List (RoseTree α)
  | _, .nil => []
  | _, .cons d ds =>
    match d with
    | .extract _ => leaf default :: remainderTraceList ds  -- replace with trace
    | .recurse c => remainderTrace c :: remainderTraceList ds
end

/-! ## §5: Sanity tests

Verify on a small concrete cut that `cutForest`, `remainderDeletion`,
and `remainderTrace` behave as expected. -/

section Tests

private def testTree : RoseTree Nat :=
  binary 0 (leaf 1) (leaf 2)
-- testTree = node 0 [node 1 [], node 2 []]

example : cutForest (emptyCut (testTree)) = [] := by
  unfold testTree binary leaf emptyCut emptyCutList cutForest cutForestList cutForestChild
  rfl

example : cutForest (shallowTotalCut testTree) = [leaf 1, leaf 2] := by
  unfold testTree binary leaf shallowTotalCut shallowTotalCut.go cutForest cutForestList cutForestChild
  rfl

example : remainderDeletion (shallowTotalCut testTree) = nary 0 [] := by
  unfold testTree binary leaf shallowTotalCut shallowTotalCut.go remainderDeletion remainderDeletionList nary
  rfl

example [Inhabited Nat] : remainderTrace (shallowTotalCut testTree) =
    binary 0 (leaf default) (leaf default) := by
  unfold testTree binary leaf shallowTotalCut shallowTotalCut.go remainderTrace remainderTraceList
  rfl

end Tests

end RoseTree
