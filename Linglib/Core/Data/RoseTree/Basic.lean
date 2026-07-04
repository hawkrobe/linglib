/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# N-ary rooted trees (rose trees)

An **n-ary rooted tree** (rose tree) over `α`: a distinguished root carrying a
value in `α`, and an ordered list of child subtrees. A leaf is `node a []`.
This is the n-ary generalization of `BinaryTree` (`Mathlib.Data.Tree.Basic`),
matching Haskell's `Data.RoseTree` (`Node a [RoseTree a]`).

The children are an ordered `List`, not a `Multiset` or a `WType` branching
family: `List`-valued children are positivity-clean, keep the type computable,
and give the ergonomic `map`/traversal API that the unordered (`Multiset`) and
`WType` encodings do not. The **unordered** rooted tree — the carrier of the
free pre-Lie algebra and the Connes–Kreimer Hopf algebra — is a *quotient* of
this type by child permutation, built downstream; it does not belong at this
data-structure layer.

## The recursion principle

The type is nested through `List`, so the auto-generated recursor hands a
per-`List` motive rather than a `∀ c ∈ children, motive c` hypothesis. The
`RoseTree.rec'` eliminator (registered `@[induction_eliminator]`) packages the
`(tree, list-of-trees)` shape once, so downstream `map`/`depth`/`numNodes`
recurse and prove with a single `List`-shaped induction hypothesis instead of a
hand-written `mutual` block per operation.

## Upstreaming

Intended shape for the reserved `Mathlib.Data.Tree` n-ary `Tree` slot (freed by
mathlib's `Tree → BinaryTree` rename). Self-contained: no linguistics, no order/command
imports. Dependency-light, `sorry`-free, no `noncomputable`.
-/


/-- An **n-ary rooted tree** (rose tree): a root `value : α` and an ordered list
of child subtrees. A leaf is `node a []`. -/
inductive RoseTree (α : Type*) where
  | node (value : α) (children : List (RoseTree α))
  deriving Repr

compile_inductive% RoseTree

namespace RoseTree

variable {α : Type*} {β : Type*} {γ : Type*}

/-! ### Projections -/

/-- The value at the root. -/
def value : RoseTree α → α
  | .node a _ => a

/-- The ordered list of child subtrees at the root. -/
def children : RoseTree α → List (RoseTree α)
  | .node _ cs => cs

@[simp] theorem value_node (a : α) (cs : List (RoseTree α)) : (node a cs).value = a := rfl

@[simp] theorem children_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).children = cs := rfl

/-- A **leaf**: a root with no children. -/
def leaf (a : α) : RoseTree α := .node a []

@[simp] theorem children_leaf (a : α) : (leaf a).children = [] := rfl

/-! ### Decidable equality

`deriving DecidableEq` does not fire through the nested `List` occurrence (still
true as of Lean v4.32.0-rc1), so the instance is built by mutual recursion on the
tree and its child list. -/

section DecidableEq
variable [DecidableEq α]

mutual

/-- Decidable equality on trees (mutual with the child-list case). -/
protected def decEq : (t s : RoseTree α) → Decidable (t = s)
  | node a cs, node b ds =>
    if hab : a = b then
      match RoseTree.decEqList cs ds with
      | isTrue h => isTrue (by rw [hab, h])
      | isFalse h => isFalse fun he => by injection he with _ hcd; exact h hcd
    else
      isFalse fun he => by injection he with hab' _; exact hab hab'

/-- Decidable equality on child lists (mutual with the tree case). -/
protected def decEqList : (ts ss : List (RoseTree α)) → Decidable (ts = ss)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | c :: cs, d :: ds =>
    match RoseTree.decEq c d with
    | isFalse h => isFalse fun he => by injection he with hcd _; exact h hcd
    | isTrue h =>
      match RoseTree.decEqList cs ds with
      | isTrue h2 => isTrue (by rw [h, h2])
      | isFalse h2 => isFalse fun he => by injection he with _ htl; exact h2 htl

end

instance instDecidableEq : DecidableEq (RoseTree α) := RoseTree.decEq

end DecidableEq

/-! ### Size -/

/-- A child of a node is strictly smaller than the node, in the auto-generated
`SizeOf`. This is the measure behind `rec'` and downstream well-founded
recursions over `RoseTree`. -/
theorem sizeOf_lt_of_mem {a : α} {cs : List (RoseTree α)} {c : RoseTree α} (hc : c ∈ cs) :
    sizeOf c < sizeOf (RoseTree.node a cs) := by
  have := List.sizeOf_lt_of_mem hc
  simp only [RoseTree.node.sizeOf_spec]
  omega

/-! ### The recursion principle -/

/-- **Structural induction** for `RoseTree`: to prove `motive t` for all `t`, prove
it for `node a cs` given `motive c` for every child `c ∈ cs`. Packages the
nested-`List` recursion so downstream defs/proofs use a single `List`-shaped
hypothesis. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : RoseTree α → Sort*}
    (node : ∀ (a : α) (cs : List (RoseTree α)),
      (∀ c ∈ cs, motive c) → motive (RoseTree.node a cs)) :
    ∀ t, motive t
  | .node a cs => node a cs fun c _hc => rec' node c
termination_by t => sizeOf t
decreasing_by exact sizeOf_lt_of_mem _hc

/-! ### Catamorphism

`fold f` is the workhorse: every structural operation (`map`, `numNodes`,
`height`, …) is a one-line `fold` specialization, and their reduction lemmas fall
out of `fold_node`. -/

mutual
/-- Catamorphism: replace each `node a cs` by `f a (folded children)`. -/
def fold (f : α → List β → β) : RoseTree α → β
  | .node a cs => f a (foldList f cs)
/-- Auxiliary: fold across a list of children. -/
def foldList (f : α → List β → β) : List (RoseTree α) → List β
  | [] => []
  | c :: cs => fold f c :: foldList f cs
end

theorem foldList_eq (f : α → List β → β) (cs : List (RoseTree α)) :
    foldList f cs = cs.map (fold f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [show foldList f (c :: cs) = fold f c :: foldList f cs from rfl,
      ih, List.map_cons]

@[simp] theorem fold_node (f : α → List β → β) (a : α) (cs : List (RoseTree α)) :
    fold f (node a cs) = f a (cs.map (fold f)) := by
  rw [show fold f (node a cs) = f a (foldList f cs) from rfl, foldList_eq]

/-! ### Functoriality -/

/-- Relabel every node by `f`, preserving shape. -/
def map (f : α → β) : RoseTree α → RoseTree β :=
  fold fun a cs => RoseTree.node (f a) cs

@[simp] theorem map_node (f : α → β) (a : α) (cs : List (RoseTree α)) :
    map f (node a cs) = node (f a) (cs.map (map f)) := by
  simp only [map, fold_node]

theorem id_map (t : RoseTree α) : map id t = t := by
  induction t with
  | node a cs ih =>
    rw [map_node, id_eq]
    congr 1
    exact (List.map_congr_left ih).trans (List.map_id cs)

theorem comp_map (f : α → β) (g : β → γ) (t : RoseTree α) :
    map (g ∘ f) t = map g (map f t) := by
  induction t with
  | node a cs ih =>
    rw [map_node, map_node, map_node, Function.comp_apply, List.map_map]
    congr 1
    exact List.map_congr_left ih

/-! ### Traversal

Effectful traversal: act on the root, then the children left-to-right — the
`Traversable` action for `RoseTree`. -/

section Traverse
universe u

mutual
/-- Traverse a tree with an applicative action, root then children in order. -/
def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    RoseTree α → m (RoseTree β)
  | .node a cs => RoseTree.node <$> f a <*> traverseList f cs
/-- Auxiliary: traverse a list of child subtrees. -/
def traverseList {m : Type u → Type u} [Applicative m] {α β : Type u} (f : α → m β) :
    List (RoseTree α) → m (List (RoseTree β))
  | [] => pure []
  | c :: cs => (· :: ·) <$> traverse f c <*> traverseList f cs
end

@[simp] theorem traverse_node {m : Type u → Type u} [Applicative m] {α β : Type u}
    (f : α → m β) (a : α) (cs : List (RoseTree α)) :
    traverse f (node a cs) = RoseTree.node <$> f a <*> traverseList f cs := rfl

private theorem traverseList_pure_of {m : Type u → Type u} [Applicative m] [LawfulApplicative m]
    {α : Type u} :
    ∀ (cs : List (RoseTree α)), (∀ c ∈ cs, traverse (pure : α → m α) c = pure c) →
      traverseList (pure : α → m α) cs = pure cs
  | [], _ => rfl
  | c :: cs, h => by
    rw [show traverseList (pure : α → m α) (c :: cs)
          = (· :: ·) <$> traverse (pure : α → m α) c <*> traverseList (pure : α → m α) cs
        from rfl,
      h c (List.mem_cons_self ..),
      traverseList_pure_of cs fun d hd => h d (List.mem_cons_of_mem _ hd)]
    simp [map_pure]

theorem traverse_pure {m : Type u → Type u} [Applicative m] [LawfulApplicative m]
    {α : Type u} (t : RoseTree α) :
    traverse (pure : α → m α) t = pure t := by
  induction t with
  | node a cs ih =>
    rw [traverse_node, traverseList_pure_of cs ih]
    simp [map_pure]

end Traverse

/-! ### Counting -/

/-- The total number of nodes (vertices). A leaf counts as `1`. -/
def numNodes : RoseTree α → ℕ :=
  fold fun _ ns => 1 + ns.sum

@[simp] theorem numNodes_node (a : α) (cs : List (RoseTree α)) :
    numNodes (node a cs) = 1 + (cs.map numNodes).sum := by
  simp only [numNodes, fold_node]

theorem numNodes_pos (t : RoseTree α) : 0 < numNodes t := by
  cases t with
  | node a cs => rw [numNodes_node]; omega

/-- The number of leaves (childless nodes). A single leaf counts as `1`. -/
def numLeaves : RoseTree α → ℕ :=
  fold fun _ ns => max 1 ns.sum

@[simp] theorem numLeaves_node (a : α) (cs : List (RoseTree α)) :
    numLeaves (node a cs) = max 1 (cs.map numLeaves).sum := by
  simp only [numLeaves, fold_node]

@[simp] theorem numLeaves_leaf (a : α) : numLeaves (leaf a) = 1 := by
  rw [leaf, numLeaves_node]; simp

theorem numLeaves_pos (t : RoseTree α) : 0 < numLeaves t := by
  cases t with
  | node a cs =>
    rw [numLeaves_node]
    exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

/-- The `(offset, size)` leaf-spans of the nodes satisfying `p`, in
left-to-right traversal order: the offset counts leaves strictly to
the node's left, the size its own leaves. -/
def spansOf (p : α → Bool) (t : RoseTree α) : List (ℕ × ℕ) := go 0 t where
  go (off : ℕ) : RoseTree α → List (ℕ × ℕ)
    | .node a cs =>
        (if p a then [(off, numLeaves (node a cs))] else []) ++ goList off cs
  goList (off : ℕ) : List (RoseTree α) → List (ℕ × ℕ)
    | [] => []
    | c :: cs => go off c ++ goList (off + numLeaves c) cs


/-- The **height** (length of the longest root-to-leaf path in edges): a leaf has
height `0`, an internal node is one more than the maximum child height. -/
def height : RoseTree α → ℕ :=
  fold fun _ ds => (ds.map (· + 1)).foldr max 0

@[simp] theorem height_node (a : α) (cs : List (RoseTree α)) :
    height (node a cs) = ((cs.map height).map (· + 1)).foldr max 0 := by
  simp only [height, fold_node]

/-! ### Arity and the leaf test -/

/-- The arity of the root: its number of children. A leaf has arity `0`. -/
def arity (t : RoseTree α) : ℕ := t.children.length

@[simp] theorem arity_node (a : α) (cs : List (RoseTree α)) : arity (node a cs) = cs.length := rfl

@[simp] theorem arity_map (f : α → β) (t : RoseTree α) : (map f t).arity = t.arity := by
  cases t with
  | node a cs => simp [arity, map_node]

/-- Whether the root is a leaf (has no children). -/
def isLeaf (t : RoseTree α) : Bool := t.children.isEmpty

@[simp] theorem isLeaf_node_nil (a : α) : isLeaf (node a []) = true := rfl

@[simp] theorem isLeaf_node_cons (a : α) (c : RoseTree α) (cs : List (RoseTree α)) :
    isLeaf (node a (c :: cs)) = false := rfl

@[simp] theorem isLeaf_map (f : α → β) (t : RoseTree α) : (map f t).isLeaf = t.isLeaf := by
  cases t with
  | node a cs => cases cs <;> simp [isLeaf, map_node]

/-! ### Smart constructors -/

/-- A **unary** node: a single child. -/
def unary (a : α) (c : RoseTree α) : RoseTree α := node a [c]
/-- A **binary** node: two ordered children. -/
def binary (a : α) (l r : RoseTree α) : RoseTree α := node a [l, r]
/-- An **n-ary** node: a list of children. -/
def nary (a : α) (cs : List (RoseTree α)) : RoseTree α := node a cs

@[simp] theorem leaf_def (a : α) : leaf a = node a [] := rfl
@[simp] theorem unary_def (a : α) (c : RoseTree α) : unary a c = node a [c] := rfl
@[simp] theorem binary_def (a : α) (l r : RoseTree α) : binary a l r = node a [l, r] := rfl
@[simp] theorem nary_def (a : α) (cs : List (RoseTree α)) : nary a cs = node a cs := rfl

/-! ### `depth` — longest root-to-leaf path in vertices

`depth = height + 1`: a leaf has depth `1` (`height` counts edges, `depth`
counts the vertices on the longest path). -/

def depth : RoseTree α → ℕ :=
  fold fun _ ds => 1 + ds.foldr max 0

@[simp] theorem depth_node (a : α) (cs : List (RoseTree α)) :
    depth (node a cs) = 1 + (cs.map depth).foldr max 0 := by
  simp only [depth, fold_node]

@[simp] theorem depth_map (f : α → β) (t : RoseTree α) : (map f t).depth = t.depth := by
  induction t with
  | node a cs ih =>
    simp only [map_node, depth_node, List.map_map]
    exact congrArg (1 + ·) (congrArg (List.foldr max 0) (List.map_congr_left ih))

/-- Each child's depth is at most the children's max depth. -/
theorem depth_le_foldr_max {c : RoseTree α} {cs : List (RoseTree α)} (h : c ∈ cs) :
    c.depth ≤ (cs.map depth).foldr max 0 := by
  induction cs with
  | nil => cases h
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The children's max depth is at most any common bound on the children. -/
theorem foldr_max_depth_le {cs : List (RoseTree α)} {n : ℕ} (h : ∀ c ∈ cs, c.depth ≤ n) :
    (cs.map depth).foldr max 0 ≤ n := by
  induction cs with
  | nil => exact Nat.zero_le n
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..),
      ih fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

/-! ### `map` preserves the counts -/

theorem map_leaf (f : α → β) (a : α) : map f (leaf a) = leaf (f a) := rfl

@[simp] theorem numNodes_map (f : α → β) (t : RoseTree α) : (map f t).numNodes = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [map_node, numNodes_node, List.map_map]
    exact congrArg (1 + ·) (congrArg List.sum (List.map_congr_left ih))

@[simp] theorem numLeaves_map (f : α → β) (t : RoseTree α) : (map f t).numLeaves = t.numLeaves := by
  induction t with
  | node a cs ih =>
    simp only [map_node, numLeaves_node, List.map_map]
    exact congrArg (max 1 ·) (congrArg List.sum (List.map_congr_left ih))

@[simp] theorem height_map (f : α → β) (t : RoseTree α) : (map f t).height = t.height := by
  induction t with
  | node a cs ih =>
    simp only [map_node, height_node, List.map_map]
    exact congrArg (List.foldr max 0) (List.map_congr_left fun c hc => congrArg (· + 1) (ih c hc))

/-! ### Instances -/

instance [Inhabited α] : Inhabited (RoseTree α) := ⟨leaf default⟩

/-! ### Sanity checks -/

example : numNodes (leaf 0 : RoseTree ℕ) = 1 := by simp [leaf]
example : numNodes (node 0 [leaf 1, leaf 2] : RoseTree ℕ) = 3 := by simp [leaf]
example : numLeaves (node 0 [leaf 1, node 2 [leaf 3, leaf 4]] : RoseTree ℕ) = 3 := by simp [leaf]
example : height (leaf 0 : RoseTree ℕ) = 0 := by simp [leaf]
example : height (node 0 [leaf 1, leaf 2] : RoseTree ℕ) = 1 := by simp [leaf]
example : height (node 0 [node 1 [leaf 2]] : RoseTree ℕ) = 2 := by simp [leaf]
example : map (· + 1) (node 0 [leaf 1] : RoseTree ℕ) = node 1 [leaf 2] := by simp [leaf]
example : traverse (m := Id) (· + 1) (node 0 [leaf 1] : RoseTree ℕ) = node 1 [leaf 2] := rfl
example : (node 0 [leaf 1] : RoseTree ℕ) = node 0 [leaf 1] := by decide
example : (node 0 [leaf 1] : RoseTree ℕ) ≠ node 0 [leaf 2] := by decide

end RoseTree

