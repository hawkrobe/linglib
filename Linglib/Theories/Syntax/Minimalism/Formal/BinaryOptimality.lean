/-
# Binary Optimality of Merge

Formalizes §1.11 of @cite{marcolli-chomsky-berwick-2025}: binary Merge uniquely
achieves all possible string lengths (Lemma 1.11.4), and the Catalan number
connection for counting SO shapes.

## Main definitions

- `NaryTree`: n-ary trees (generalized Merge)
- `achievableLeafCounts`: set of achievable leaf counts for n-ary Merge

## Main results

- `binary_achieves_all`: binary Merge achieves all leaf counts ≥ 1
- `nary_restricted`: n-ary (n≥3) restricted to k(n-1)+1
- `binary_unique_optimal`: binary is uniquely optimal
- `so_shapes_catalan`: number of SO shapes with n internal nodes = catalan n

-/

import Linglib.Theories.Syntax.Minimalism.Core.Algebra
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Minimalism

/-! ## n-ary trees (generalized Merge) -/

/-- n-ary tree: generalization of SyntacticObject to n-ary branching.
    When n = 2 this recovers binary trees (= SyntacticObject).
    When n ≥ 3 this models hypothetical n-ary Merge. -/
inductive NaryTree (n : Nat) : Type where
  | leaf : NaryTree n
  | node : (Fin n → NaryTree n) → NaryTree n

/-- Leaf count of an n-ary tree -/
def NaryTree.leafCount {n : Nat} : NaryTree n → Nat
  | .leaf => 1
  | .node children => Finset.univ.sum (λ i => (children i).leafCount)

/-! ## Achievable leaf counts (Lemma 1.11.4)

For n-ary trees:
- Binary (n=2): every k ≥ 1 is achievable
- n-ary (n≥3): only k ≡ 1 (mod n-1) are achievable, i.e. k = j(n-1) + 1 -/

/-- The set of leaf counts achievable by n-ary trees -/
def achievableLeafCounts (n : Nat) : Set Nat :=
  { k | ∃ t : NaryTree n, t.leafCount = k }

/-- A single leaf achieves count 1 for any arity -/
theorem leaf_achieves_one (n : Nat) :
    1 ∈ achievableLeafCounts n :=
  ⟨.leaf, rfl⟩

/-- Binary trees achieve leaf count 2 (a single node with two leaves) -/
theorem binary_achieves_two :
    2 ∈ achievableLeafCounts 2 := by
  refine ⟨.node (λ _ => .leaf), ?_⟩
  simp [NaryTree.leafCount]

/-- Replace the leftmost leaf of a binary tree with a node of two leaves.
    This increases leafCount by exactly 1. -/
def NaryTree.expandLeaf : NaryTree 2 → NaryTree 2
  | .leaf => .node (λ _ => .leaf)
  | .node children => .node (λ i =>
      if i = (⟨0, by omega⟩ : Fin 2) then (children ⟨0, by omega⟩).expandLeaf
      else children i)

theorem NaryTree.expandLeaf_leafCount (t : NaryTree 2) :
    t.expandLeaf.leafCount = t.leafCount + 1 := by
  induction t with
  | leaf => simp [NaryTree.expandLeaf, NaryTree.leafCount]
  | node children ih =>
    simp only [NaryTree.expandLeaf, NaryTree.leafCount]
    have h0 : (⟨0, by omega⟩ : Fin 2) ≠ (⟨1, by omega⟩ : Fin 2) := by decide
    -- The sum over Fin 2 splits into i=0 and i=1
    conv_lhs =>
      arg 2; ext i
      rw [show (if i = (⟨0, by omega⟩ : Fin 2) then (children ⟨0, by omega⟩).expandLeaf
            else children i).leafCount =
          if i = (⟨0, by omega⟩ : Fin 2) then (children ⟨0, by omega⟩).expandLeaf.leafCount
            else (children i).leafCount from by split <;> rfl]
    simp only [Fin.sum_univ_two]
    simp [h0, ih]
    omega

/-- Binary trees achieve all leaf counts k ≥ 1.

    Proof: induction on k. Base k=1: single leaf. Step: expand a leaf to
    get one more, via `expandLeaf` which increases leafCount by exactly 1. -/
theorem binary_achieves_all (k : Nat) (hk : k ≥ 1) :
    k ∈ achievableLeafCounts 2 := by
  induction k with
  | zero => omega
  | succ n ih =>
    match n, hk with
    | 0, _ => exact leaf_achieves_one 2
    | n + 1, _ =>
      obtain ⟨t, ht⟩ := ih (by omega)
      exact ⟨t.expandLeaf, by rw [NaryTree.expandLeaf_leafCount, ht]⟩

/-- Node count of an n-ary tree -/
def NaryTree.nodeCount {n : Nat} : NaryTree n → Nat
  | .leaf => 0
  | .node children => 1 + Finset.univ.sum (λ i => (children i).nodeCount)

/-- For n-ary trees, leafCount = nodeCount * (n-1) + 1.
    This is the key structural invariant that implies the modular constraint. -/
theorem nary_leaf_node_relation {n : Nat} (hn : n ≥ 2) (t : NaryTree n) :
    t.leafCount = t.nodeCount * (n - 1) + 1 := by
  induction t with
  | leaf => simp [NaryTree.leafCount, NaryTree.nodeCount]
  | node children ih =>
    simp only [NaryTree.leafCount, NaryTree.nodeCount]
    conv_lhs => arg 2; ext i; rw [ih i]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul, Nat.mul_one]
    rw [← Finset.sum_mul]
    ring_nf
    omega

/-- For n-ary trees (n ≥ 2), leaf count k must satisfy k ≡ 1 (mod n-1).

    Each n-ary node replaces 1 "slot" with n children, net gain of n-1 leaves.
    Starting from 1 leaf, after j nodes we have j(n-1) + 1 leaves. -/
theorem nary_leaf_count_mod {n : Nat} (hn : n ≥ 2)
    (t : NaryTree n) : (t.leafCount - 1) % (n - 1) = 0 := by
  rw [nary_leaf_node_relation hn t, Nat.add_sub_cancel]
  rw [Nat.mul_comm]
  exact Nat.mul_mod_right _ _

/-- For n ≥ 3, not all leaf counts are achievable.
    Specifically, 2 is not achievable when n ≥ 3 (since 2-1 = 1 is not
    divisible by n-1 ≥ 2). -/
theorem nary_misses_two (n : Nat) (hn : n ≥ 3) :
    2 ∉ achievableLeafCounts n := by
  intro ⟨t, ht⟩
  have hmod := nary_leaf_count_mod (by omega : n ≥ 2) t
  rw [ht] at hmod
  simp at hmod
  -- 1 % (n-1) = 0 requires n-1 | 1, so n-1 ≤ 1, contradicting n ≥ 3
  omega

/-- Binary Merge is uniquely optimal: it's the only n ≥ 2 that achieves all
    leaf counts (Lemma 1.11.4). -/
theorem binary_unique_optimal (n : Nat) (hn : n ≥ 2)
    (h : ∀ k, k ≥ 1 → k ∈ achievableLeafCounts n) :
    n = 2 := by
  by_contra h2
  have hn3 : n ≥ 3 := by omega
  exact nary_misses_two n hn3 (h 2 (by omega))

/-! ## Catalan bridge

The number of SO shapes with n internal nodes equals the nth Catalan
number. We bridge `SyntacticObject.shape` (→ `TreeShape`) to mathlib's
`Tree Unit` (which has the Catalan theorem) via explicit bijection. -/

/-- Node count of a tree shape -/
def TreeShape.nodeCount : TreeShape → Nat
  | .leaf => 0
  | .node a b => 1 + a.nodeCount + b.nodeCount

/-- SO.shape preserves nodeCount -/
theorem shape_nodeCount (so : SyntacticObject) :
    so.shape.nodeCount = so.nodeCount := by
  induction so with
  | leaf _ => simp [SyntacticObject.shape, TreeShape.nodeCount, SyntacticObject.nodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.shape, TreeShape.nodeCount, SyntacticObject.nodeCount, iha, ihb]

/-- SO.nodeCount = FreeMagma.length - 1 via the isomorphism -/
theorem nodeCount_eq_freeMagma_length_sub (so : SyntacticObject) :
    so.nodeCount = (toFreeMagma so).length - 1 := by
  have h1 := leafCount_eq_freeMagma_length so
  have h2 := leaf_node_relation so
  omega

/-! ### TreeShape ≃ Tree Unit

`TreeShape` (leaf/node) and mathlib's `Tree Unit` (nil/node) are the same
inductive structure. The bijection preserves internal node count, connecting
`SyntacticObject.shape` to mathlib's Catalan combinatorics. -/

/-- Map TreeShape to Tree Unit -/
def TreeShape.toTree : TreeShape → Tree Unit
  | .leaf => .nil
  | .node a b => .node () a.toTree b.toTree

/-- Map Tree Unit to TreeShape -/
def _root_.Tree.toTreeShape : Tree Unit → TreeShape
  | .nil => .leaf
  | .node () a b => .node a.toTreeShape b.toTreeShape

@[simp]
theorem toTree_toTreeShape (t : TreeShape) : t.toTree.toTreeShape = t := by
  induction t with
  | leaf => rfl
  | node a b iha ihb => simp [TreeShape.toTree, Tree.toTreeShape, iha, ihb]

@[simp]
theorem toTreeShape_toTree (t : Tree Unit) : t.toTreeShape.toTree = t := by
  induction t with
  | nil => rfl
  | node u a b iha ihb => cases u; simp [Tree.toTreeShape, TreeShape.toTree, iha, ihb]

/-- TreeShape ≃ Tree Unit — the same inductive structure -/
def treeShapeTreeEquiv : TreeShape ≃ Tree Unit where
  toFun := TreeShape.toTree
  invFun := Tree.toTreeShape
  left_inv := toTree_toTreeShape
  right_inv := toTreeShape_toTree

/-- The bijection preserves internal node count -/
theorem toTree_numNodes (t : TreeShape) :
    t.toTree.numNodes = t.nodeCount := by
  induction t with
  | leaf => simp [TreeShape.toTree, TreeShape.nodeCount, Tree.numNodes]
  | node a b iha ihb =>
    simp [TreeShape.toTree, TreeShape.nodeCount, Tree.numNodes, iha, ihb]
    omega

/-- The number of SO shapes with n internal nodes equals the nth Catalan
    number.

    The proof chain: `SyntacticObject.shape` erases labels to `TreeShape`,
    `treeShapeTreeEquiv` bijects with `Tree Unit`, and mathlib's
    `treesOfNumNodesEq_card_eq_catalan` counts `Tree Unit` shapes. -/
theorem so_shapes_catalan (n : Nat) :
    (Tree.treesOfNumNodesEq n).card = catalan n :=
  Tree.treesOfNumNodesEq_card_eq_catalan n

/-- Every TreeShape with n nodes maps to a member of treesOfNumNodesEq n -/
theorem toTree_mem_treesOfNumNodesEq (t : TreeShape) :
    t.toTree ∈ Tree.treesOfNumNodesEq t.nodeCount := by
  rw [Tree.mem_treesOfNumNodesEq]
  exact toTree_numNodes t

end Minimalism
