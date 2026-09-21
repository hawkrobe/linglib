/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Order.Nat

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
`(tree, list-of-trees)` shape once, so downstream `map`/`height`/`numNodes`
recurse and prove with a single `List`-shaped induction hypothesis instead of a
hand-written `mutual` block per operation.
-/

@[expose] public section


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
abbrev leaf (a : α) : RoseTree α := .node a []

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
theorem sizeOf_lt_of_mem [SizeOf α] {a : α} {cs : List (RoseTree α)} {c : RoseTree α}
    (hc : c ∈ cs) : sizeOf c < sizeOf (RoseTree.node a cs) := by
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

/-- Fusion: postcomposing a fold with `h` is the fold of the pushed-forward algebra —
the `RoseTree` sibling of `List.foldr_hom`. -/
theorem fold_hom (h : β → γ) {f : α → List β → β} {g : α → List γ → γ}
    (hfg : ∀ a ps, h (f a ps) = g a (ps.map h)) (t : RoseTree α) :
    h (fold f t) = fold g t := by
  induction t with
  | node a cs ih =>
    rw [fold_node, fold_node, hfg, List.map_map]
    exact congrArg (g a) (List.map_congr_left fun c hc => ih c hc)

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
  fold fun _ ns => ns.sum + 1

@[simp] theorem numNodes_node (a : α) (cs : List (RoseTree α)) :
    numNodes (node a cs) = (cs.map numNodes).sum + 1 := by
  simp only [numNodes, fold_node]

theorem numNodes_pos (t : RoseTree α) : 0 < numNodes t := by
  cases t with
  | node a cs => rw [numNodes_node]; omega

/-- The node values in preorder: root first, then each child's values
left to right. -/
def values : RoseTree α → List α :=
  fold fun a ls => a :: ls.flatten

@[simp] theorem values_node (a : α) (cs : List (RoseTree α)) :
    values (node a cs) = a :: (cs.map values).flatten := by
  simp only [values, fold_node]

theorem length_values (t : RoseTree α) : t.values.length = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [values_node, numNodes_node, List.length_cons, List.length_flatten,
      List.map_map, Function.comp_def]
    rw [show (cs.map fun c => c.values.length) = cs.map numNodes from
      List.map_congr_left ih]

mutual
/-- The value at each node paired with the values of its children, in preorder: the local
branching structure of the tree, one entry per node. -/
def offspring : RoseTree α → List (α × List α)
  | .node a cs => (a, cs.map value) :: offspringList cs
/-- Auxiliary: the offspring entries of a list of trees, concatenated. -/
def offspringList : List (RoseTree α) → List (α × List α)
  | [] => []
  | c :: cs => offspring c ++ offspringList cs
end

theorem offspringList_eq (cs : List (RoseTree α)) :
    offspringList cs = (cs.map offspring).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [offspringList, ih, List.map_cons, List.flatten_cons]

@[simp] theorem offspring_node (a : α) (cs : List (RoseTree α)) :
    offspring (node a cs) = (a, cs.map value) :: (cs.map offspring).flatten := by
  rw [offspring, offspringList_eq]

theorem length_offspring (t : RoseTree α) : t.offspring.length = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [offspring_node, numNodes_node, List.length_cons, List.length_flatten,
      List.map_map, Function.comp_def]
    rw [show (cs.map fun c => c.offspring.length) = cs.map numNodes from
      List.map_congr_left ih]

/-- The leaf values from left to right: the ordered frontier. -/
def leafList : RoseTree α → List α :=
  fold fun a ls => match ls with
    | [] => [a]
    | ls => ls.flatten

@[simp] theorem leafList_leaf (a : α) : leafList (node a []) = [a] := by
  simp only [leafList, fold_node, List.map_nil]

theorem leafList_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    leafList (node a cs) = (cs.map leafList).flatten := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [leafList, fold_node, List.map_cons]

@[simp] theorem leafList_node_cons (a : α) (c : RoseTree α) (cs : List (RoseTree α)) :
    leafList (node a (c :: cs)) = ((c :: cs).map leafList).flatten :=
  leafList_node_of_ne_nil a (List.cons_ne_nil c cs)

theorem leafList_ne_nil (t : RoseTree α) : t.leafList ≠ [] := by
  induction t with
  | node a cs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      rw [leafList_node_cons]
      exact List.flatten_ne_nil_iff.2 ⟨c.leafList, List.mem_map_of_mem (List.mem_cons_self ..),
        ih c (List.mem_cons_self ..)⟩

/-- The number of leaves (childless nodes). A single leaf counts as `1`. -/
def numLeaves : RoseTree α → ℕ :=
  fold fun _ ns => max 1 ns.sum

@[simp] theorem numLeaves_node (a : α) (cs : List (RoseTree α)) :
    numLeaves (node a cs) = max 1 (cs.map numLeaves).sum := by
  simp only [numLeaves, fold_node]

@[simp] theorem numLeaves_leaf (a : α) : numLeaves (leaf a) = 1 := by simp

theorem numLeaves_pos (t : RoseTree α) : 0 < numLeaves t := by
  cases t with
  | node a cs =>
    rw [numLeaves_node]
    exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

/-! ### Height -/

/-- The **height**: the number of vertices on a longest root-to-leaf path, so a leaf has
height `1`. This is the convention of `BinaryTree.height`, where `nil` has height `0`. -/
def height : RoseTree α → ℕ :=
  fold fun _ hs => hs.foldr max 0 + 1

@[simp] theorem height_node (a : α) (cs : List (RoseTree α)) :
    height (node a cs) = (cs.map height).foldr max 0 + 1 := by
  simp only [height, fold_node]

theorem height_pos (t : RoseTree α) : 0 < t.height := by
  cases t with
  | node a cs => rw [height_node]; exact Nat.succ_pos _

theorem height_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.height < t.height := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [height_node]
    exact Nat.lt_succ_of_le (List.le_max_of_le (l := cs.map height) (List.mem_map_of_mem h) le_rfl)

/-! ### Arity -/

/-- The arity of the root: its number of children. A leaf has arity `0`. -/
def arity (t : RoseTree α) : ℕ := t.children.length

@[simp] theorem arity_node (a : α) (cs : List (RoseTree α)) : arity (node a cs) = cs.length := rfl

@[simp] theorem arity_map (f : α → β) (t : RoseTree α) : (map f t).arity = t.arity := by
  cases t with
  | node a cs => simp [arity, map_node]

/-! ### `map` preserves the counts -/

@[simp] theorem map_leaf (f : α → β) (a : α) : map f (leaf a) = leaf (f a) := rfl

@[simp] theorem numNodes_map (f : α → β) (t : RoseTree α) : (map f t).numNodes = t.numNodes := by
  induction t with
  | node a cs ih =>
    simp only [map_node, numNodes_node, List.map_map]
    exact congrArg (· + 1) (congrArg List.sum (List.map_congr_left ih))

@[simp] theorem numLeaves_map (f : α → β) (t : RoseTree α) : (map f t).numLeaves = t.numLeaves := by
  induction t with
  | node a cs ih =>
    simp only [map_node, numLeaves_node, List.map_map]
    exact congrArg (max 1 ·) (congrArg List.sum (List.map_congr_left ih))

@[simp] theorem height_map (f : α → β) (t : RoseTree α) : (map f t).height = t.height := by
  induction t with
  | node a cs ih =>
    simp only [map_node, height_node, List.map_map]
    exact congrArg (· + 1) (congrArg (List.foldr max 0) (List.map_congr_left ih))

@[simp] theorem offspring_map (f : α → β) (t : RoseTree α) :
    (map f t).offspring = t.offspring.map fun p => (f p.1, p.2.map f) := by
  induction t with
  | node a cs ih =>
    simp only [map_node, offspring_node, List.map_map, List.map_cons, List.map_flatten]
    refine congrArg₂ _ ?_ (congrArg List.flatten (List.map_congr_left fun c hc => ih c hc))
    exact congrArg _ (List.map_congr_left fun c _ => by cases c; rfl)

@[simp] theorem leafList_map (f : α → β) (t : RoseTree α) :
    (map f t).leafList = t.leafList.map f := by
  induction t with
  | node a cs ih =>
    cases cs with
    | nil => simp
    | cons c cs =>
      simp only [map_node, List.map_cons, leafList_node_cons, List.map_flatten, List.map_map]
      exact congrArg List.flatten (congrArg₂ _ (ih c (List.mem_cons_self ..))
        (List.map_congr_left fun d hd => ih d (List.mem_cons_of_mem _ hd)))

/-! ### Instances -/

instance [Inhabited α] : Inhabited (RoseTree α) := ⟨leaf default⟩

end RoseTree

