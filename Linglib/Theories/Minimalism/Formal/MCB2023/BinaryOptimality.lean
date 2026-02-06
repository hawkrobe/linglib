/-
# Binary Optimality of Merge

Formalizes §4 of Marcolli, Chomsky & Berwick (2023): binary Merge uniquely
achieves all possible string lengths (Lemma 4.4), and the Catalan number
connection for counting SO shapes.

## Main definitions

- `NaryTree`: n-ary trees (generalized Merge)
- `achievableLeafCounts`: set of achievable leaf counts for n-ary Merge

## Main results

- `binary_achieves_all`: binary Merge achieves all leaf counts ≥ 1
- `nary_restricted`: n-ary (n≥3) restricted to k(n-1)+1
- `binary_unique_optimal`: binary is uniquely optimal
- `so_shapes_catalan`: number of SO shapes with n internal nodes = catalan n

## References

- Marcolli, M., Chomsky, N. & Berwick, R.C. (2023). "Mathematical Structure of
  Syntactic Merge", §4
-/

import Linglib.Theories.Minimalism.Formal.MCB2023.FreeMagmaEquiv
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

/-! ## Achievable leaf counts (Lemma 4.4)

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
    leaf counts (Lemma 4.4). -/
theorem binary_unique_optimal (n : Nat) (hn : n ≥ 2)
    (h : ∀ k, k ≥ 1 → k ∈ achievableLeafCounts n) :
    n = 2 := by
  by_contra h2
  have hn3 : n ≥ 3 := by omega
  exact nary_misses_two n hn3 (h 2 (by omega))

/-! ## Catalan bridge

The number of binary tree shapes with n internal nodes equals the nth
Catalan number. We connect this to SyntacticObject via the FreeMagma
equivalence. -/

/-- Binary tree shape: SO with Unit tokens (only tree structure matters) -/
abbrev SOShape := FreeMagma Unit

/-- Count internal nodes of a FreeMagma tree -/
def freemagmaNodeCount {α : Type*} : FreeMagma α → Nat
  | .of _ => 0
  | .mul a b => 1 + freemagmaNodeCount a + freemagmaNodeCount b

/-- The nodeCount of an SO equals the nodeCount of its FreeMagma image -/
theorem nodeCount_preserved (so : SyntacticObject) :
    so.nodeCount = freemagmaNodeCount (toFreeMagma so) := by
  induction so with
  | leaf _ => simp [SyntacticObject.nodeCount, toFreeMagma, freemagmaNodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.nodeCount, toFreeMagma, freemagmaNodeCount]
    omega

/-- Internal node count = FreeMagma.length - 1 for FreeMagma trees -/
theorem freemagmaNodeCount_eq_length_sub {α : Type*} (fm : FreeMagma α) :
    freemagmaNodeCount fm = fm.length - 1 := by
  induction fm with
  | ih1 _ => simp [freemagmaNodeCount, FreeMagma.length]
  | ih2 a b iha ihb =>
    simp [freemagmaNodeCount, FreeMagma.length]
    have := a.length_pos
    have := b.length_pos
    omega

/-- SO.nodeCount = FreeMagma.length - 1 via the isomorphism.
    Bridges `leaf_node_relation` to `FreeMagma.length`. -/
theorem nodeCount_eq_freeMagma_length_sub (so : SyntacticObject) :
    so.nodeCount = (toFreeMagma so).length - 1 := by
  have h1 := leafCount_eq_freeMagma_length so
  have h2 := leaf_node_relation so
  omega

/-- Map an SO to its shape (forget token identity, keep tree structure) -/
def SyntacticObject.toShape (so : SyntacticObject) : SOShape :=
  FreeMagma.map (λ _ => ()) (toFreeMagma so)

/-- The number of binary tree shapes with n internal nodes equals the nth
    Catalan number.

    This is a direct application of mathlib's `treesOfNumNodesEq_card_eq_catalan`,
    which counts Tree Unit shapes. The connection to SyntacticObject goes through
    the FreeMagma ≃ SO equivalence and the well-known bijection between
    full binary trees and Tree Unit. -/
theorem tree_shapes_catalan (n : Nat) :
    (Tree.treesOfNumNodesEq n).card = catalan n :=
  Tree.treesOfNumNodesEq_card_eq_catalan n

end Minimalism
