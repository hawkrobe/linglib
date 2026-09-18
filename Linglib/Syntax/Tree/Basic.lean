import Mathlib.Data.Finset.Basic
import Linglib.Core.Order.Branching

/-!
# Constituency trees

A **constituency tree** over a category type `C` and a word type `W`: a terminal carries a
category and a word, an internal node a category and an ordered list of daughters, and the
two nodes of Heim and Kratzer's trace theory of movement, an indexed trace and an indexed
binder over a body, carry a category each. Type-driven interpretation reads the tree with
`C = Unit`; structural operations on parse trees read it with a category system such as
`Syntax.Cat`.

## Main declarations

* `Syntax.Tree`: the tree, with `leaf`, `bin`, `tr` and `binder` building category-free trees.
* `Syntax.Tree.fold`: the catamorphism; `map`, `numNodes`, `terminals`, `yield`, `cats`,
  `freeIndices` and `leafSubst` are its specializations, each reducing at every constructor.
* `Syntax.Tree.rec'`: structural induction with a membership hypothesis at a node.
* `Syntax.Tree.subtrees`: the subtrees in pre-order.
* `Syntax.Tree.freeIndices` and `Syntax.Tree.Closed`: the indices of the traces no binder
  binds, and the trees with none.
* The `Core.Order.Branching` instance, through which a tree takes Gorn addresses, the
  dominance order on its positions and the command relations.

## Implementation notes

Daughters are a `List`, so a node is binary or n-ary by its list and sibling order is linear
precedence. Only the trace theory of movement is expressible: a copy or a multidominance
representation is not a tree over these constructors. That each binder binds a trace of its
index is a property of a tree, not a guarantee of the type, and interpretation does not read
the category on a binder. `deriving DecidableEq` does not fire through the nested `List`, so
the instance is built by mutual recursion with the daughter list.

## References

* [heim-kratzer-1998]
* [katzir-2007]
* [barker-pullum-1990]
-/

namespace Syntax

/-- A constituency tree: `terminal c w` is the word `w` under category `c`, `node c cs` the
category `c` over daughters `cs`, `trace n c` a trace of index `n` and `bind n c t` a binder
of index `n` over `t`. -/
inductive Tree (C W : Type*) where
  | terminal : C → W → Tree C W
  | node : C → List (Tree C W) → Tree C W
  | trace : ℕ → C → Tree C W
  | bind : ℕ → C → Tree C W → Tree C W
  deriving Repr

namespace Tree

variable {C W : Type*}

/-! ### Trees without categories -/

@[match_pattern] abbrev leaf (w : W) : Tree Unit W := .terminal () w
@[match_pattern] abbrev bin (t₁ t₂ : Tree Unit W) : Tree Unit W := .node () [t₁, t₂]
@[match_pattern] abbrev tr (n : ℕ) : Tree Unit W := .trace n ()
@[match_pattern] abbrev binder (n : ℕ) (t : Tree Unit W) : Tree Unit W := .bind n () t

/-- The category at the root. -/
@[simp] def cat : Tree C W → C
  | terminal c _ => c
  | node c _ => c
  | trace _ c => c
  | bind _ c _ => c

/-! ### Decidable equality -/

section DecidableEq
variable [DecidableEq C] [DecidableEq W]

mutual
/-- Decidable equality on trees, mutually with the daughter list. -/
protected def decEq : (t s : Tree C W) → Decidable (t = s)
  | terminal c w, terminal c' w' => decidable_of_iff (c = c' ∧ w = w') (by simp)
  | node c cs, node c' cs' =>
    match Tree.decEqList cs cs' with
    | isTrue h => decidable_of_iff (c = c') (by simp [h])
    | isFalse h => isFalse (by simp [h])
  | trace n c, trace n' c' => decidable_of_iff (n = n' ∧ c = c') (by simp)
  | bind n c t, bind n' c' t' =>
    match Tree.decEq t t' with
    | isTrue h => decidable_of_iff (n = n' ∧ c = c') (by simp [h])
    | isFalse h => isFalse (by simp [h])
  | terminal _ _, node _ _ | terminal _ _, trace _ _ | terminal _ _, bind _ _ _
  | node _ _, terminal _ _ | node _ _, trace _ _ | node _ _, bind _ _ _
  | trace _ _, terminal _ _ | trace _ _, node _ _ | trace _ _, bind _ _ _
  | bind _ _ _, terminal _ _ | bind _ _ _, node _ _ | bind _ _ _, trace _ _ =>
    isFalse (by simp)
/-- Decidable equality on daughter lists. -/
protected def decEqList : (ts ss : List (Tree C W)) → Decidable (ts = ss)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by simp)
  | t :: ts, s :: ss =>
    match Tree.decEq t s, Tree.decEqList ts ss with
    | isTrue h, isTrue hs => isTrue (by rw [h, hs])
    | isFalse h, _ => isFalse (by simp [h])
    | _, isFalse hs => isFalse (by simp [hs])
end

instance instDecidableEq : DecidableEq (Tree C W) := Tree.decEq

end DecidableEq

/-! ### The recursion principle -/

/-- A daughter is smaller than its node in the auto-generated `SizeOf`. -/
theorem sizeOf_lt_of_mem [SizeOf C] [SizeOf W] {c : C} {cs : List (Tree C W)} {t : Tree C W}
    (h : t ∈ cs) : sizeOf t < sizeOf (node c cs) := by
  have := List.sizeOf_lt_of_mem h
  simp only [node.sizeOf_spec]
  omega

/-- **Structural induction** for `Tree`: the node case has the motive at every daughter. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : Tree C W → Sort*} (terminal : ∀ c w, motive (terminal c w))
    (node : ∀ c cs, (∀ t ∈ cs, motive t) → motive (node c cs))
    (trace : ∀ n c, motive (trace n c))
    (bind : ∀ n c t, motive t → motive (bind n c t)) : ∀ t, motive t
  | .terminal c w => terminal c w
  | .node c cs => node c cs fun t _ht => rec' terminal node trace bind t
  | .trace n c => trace n c
  | .bind n c t => bind n c t (rec' terminal node trace bind t)
termination_by t => sizeOf t
decreasing_by
  · exact sizeOf_lt_of_mem _ht
  · simp only [bind.sizeOf_spec]; omega

/-! ### Catamorphism

`fold` replaces each constructor by an operation on the folded daughters; the structural
operations below are its specializations, and their reduction lemmas follow from `fold_node`.
-/

section Fold

variable {β : Type*} (terminal : C → W → β) (node : C → List β → β)
  (trace : ℕ → C → β) (bind : ℕ → C → β → β)

mutual
/-- Replace each constructor by the corresponding operation. -/
def fold : Tree C W → β
  | .terminal c w => terminal c w
  | .node c cs => node c (foldList cs)
  | .trace n c => trace n c
  | .bind n c t => bind n c (fold t)
/-- `fold` across a daughter list. -/
def foldList : List (Tree C W) → List β
  | [] => []
  | t :: ts => fold t :: foldList ts
end

theorem foldList_eq (cs : List (Tree C W)) :
    foldList terminal node trace bind cs = cs.map (fold terminal node trace bind) := by
  induction cs with
  | nil => rfl
  | cons t ts ih => rw [foldList, ih, List.map_cons]

@[simp] theorem fold_terminal (c : C) (w : W) :
    fold terminal node trace bind (.terminal c w) = terminal c w := rfl

@[simp] theorem fold_node (c : C) (cs : List (Tree C W)) :
    fold terminal node trace bind (.node c cs)
      = node c (cs.map (fold terminal node trace bind)) := by
  rw [fold, foldList_eq]

@[simp] theorem fold_trace (n : ℕ) (c : C) :
    fold terminal node trace bind (.trace n c) = trace n c := rfl

@[simp] theorem fold_bind (n : ℕ) (c : C) (t : Tree C W) :
    fold terminal node trace bind (.bind n c t) = bind n c (fold terminal node trace bind t) :=
  rfl

end Fold

/-! ### Relabelling the words -/

section Map

variable {W' W'' : Type*}

/-- Relabel the words, keeping the shape. -/
def map (f : W → W') : Tree C W → Tree C W' :=
  fold (fun c w => .terminal c (f w)) .node .trace .bind

@[simp] theorem map_terminal (f : W → W') (c : C) (w : W) :
    map f (.terminal c w) = .terminal c (f w) := rfl

@[simp] theorem map_node (f : W → W') (c : C) (cs : List (Tree C W)) :
    map f (.node c cs) = .node c (cs.map (map f)) := by
  simp only [map, fold_node]

@[simp] theorem map_trace (f : W → W') (n : ℕ) (c : C) : map f (.trace n c) = .trace n c := rfl

@[simp] theorem map_bind (f : W → W') (n : ℕ) (c : C) (t : Tree C W) :
    map f (.bind n c t) = .bind n c (map f t) := rfl

@[simp] theorem map_id (t : Tree C W) : t.map id = t := by
  induction t with
  | node c cs ih => rw [map_node, List.map_congr_left ih, List.map_id']
  | bind n c t ih => rw [map_bind, ih]
  | _ => rfl

@[simp] theorem map_map (g : W' → W'') (f : W → W') (t : Tree C W) :
    (t.map f).map g = t.map (g ∘ f) := by
  induction t with
  | node c cs ih => simp only [map_node, List.map_map]; exact congrArg _ (List.map_congr_left ih)
  | bind n c t ih => rw [map_bind, map_bind, map_bind, ih]
  | _ => rfl

@[simp] theorem cat_map (f : W → W') (t : Tree C W) : (t.map f).cat = t.cat := by
  cases t <;> rfl

end Map

/-! ### Counting -/

/-- The number of nodes. -/
def numNodes : Tree C W → ℕ :=
  fold (fun _ _ => 1) (fun _ ns => ns.sum + 1) (fun _ _ => 1) fun _ _ n => n + 1

@[simp] theorem numNodes_terminal (c : C) (w : W) : (terminal c w).numNodes = 1 := rfl

@[simp] theorem numNodes_node (c : C) (cs : List (Tree C W)) :
    (node c cs).numNodes = (cs.map numNodes).sum + 1 := by
  simp only [numNodes, fold_node]

@[simp] theorem numNodes_trace (n : ℕ) (c : C) : (trace n c : Tree C W).numNodes = 1 := rfl

@[simp] theorem numNodes_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).numNodes = t.numNodes + 1 := rfl

/-! ### The frontier -/

/-- The terminals, left to right, each with its category. -/
def terminals : Tree C W → List (C × W) :=
  fold (fun c w => [(c, w)]) (fun _ => List.flatten) (fun _ _ => []) fun _ _ ws => ws

/-- The yield: the words at the terminals, left to right. -/
def yield (t : Tree C W) : List W := t.terminals.map Prod.snd

@[simp] theorem terminals_terminal (c : C) (w : W) : (terminal c w).terminals = [(c, w)] := rfl

@[simp] theorem terminals_node (c : C) (cs : List (Tree C W)) :
    (node c cs).terminals = cs.flatMap terminals := by
  simp only [terminals, fold_node, List.flatMap_def]

@[simp] theorem terminals_trace (n : ℕ) (c : C) : (trace n c : Tree C W).terminals = [] := rfl

@[simp] theorem terminals_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).terminals = t.terminals := rfl

@[simp] theorem yield_terminal (c : C) (w : W) : (terminal c w).yield = [w] := rfl

@[simp] theorem yield_node (c : C) (cs : List (Tree C W)) :
    (node c cs).yield = cs.flatMap yield := by
  simp only [yield, terminals_node, List.map_flatMap]; rfl

@[simp] theorem yield_trace (n : ℕ) (c : C) : (trace n c : Tree C W).yield = [] := rfl

@[simp] theorem yield_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).yield = t.yield := rfl

/-! ### Categories and subtrees -/

/-- The categories at the nodes, in pre-order. -/
def cats : Tree C W → List C :=
  fold (fun c _ => [c]) (fun c css => c :: css.flatten) (fun _ c => [c]) fun _ c cs => c :: cs

@[simp] theorem cats_terminal (c : C) (w : W) : (terminal c w).cats = [c] := rfl

@[simp] theorem cats_node (c : C) (cs : List (Tree C W)) :
    (node c cs).cats = c :: cs.flatMap cats := by
  simp only [cats, fold_node, List.flatMap_def]

@[simp] theorem cats_trace (n : ℕ) (c : C) : (trace n c : Tree C W).cats = [c] := rfl

@[simp] theorem cats_bind (n : ℕ) (c : C) (t : Tree C W) : (bind n c t).cats = c :: t.cats := rfl

theorem mem_cats_node {c' c : C} {cs : List (Tree C W)} :
    c' ∈ (node c cs).cats ↔ c' = c ∨ ∃ t ∈ cs, c' ∈ t.cats := by
  simp

theorem mem_cats_bind {c' : C} {n : ℕ} {c : C} {t : Tree C W} :
    c' ∈ (bind n c t).cats ↔ c' = c ∨ c' ∈ t.cats := by
  simp

mutual
/-- The subtrees, the tree itself first, in pre-order. -/
def subtrees : Tree C W → List (Tree C W)
  | t@(.terminal _ _) => [t]
  | t@(.node _ cs) => t :: subtreesList cs
  | t@(.trace _ _) => [t]
  | t@(.bind _ _ s) => t :: subtrees s
/-- `subtrees` across a daughter list. -/
def subtreesList : List (Tree C W) → List (Tree C W)
  | [] => []
  | t :: ts => subtrees t ++ subtreesList ts
end

theorem subtreesList_eq (cs : List (Tree C W)) : subtreesList cs = cs.flatMap subtrees := by
  induction cs with
  | nil => rfl
  | cons t ts ih => rw [subtreesList, ih, List.flatMap_cons]

@[simp] theorem subtrees_terminal (c : C) (w : W) : (terminal c w).subtrees = [terminal c w] :=
  rfl

@[simp] theorem subtrees_node (c : C) (cs : List (Tree C W)) :
    (node c cs).subtrees = node c cs :: cs.flatMap subtrees := by
  rw [subtrees, subtreesList_eq]

@[simp] theorem subtrees_trace (n : ℕ) (c : C) : (trace n c : Tree C W).subtrees = [trace n c] :=
  rfl

@[simp] theorem subtrees_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).subtrees = bind n c t :: t.subtrees := rfl

theorem self_mem_subtrees (t : Tree C W) : t ∈ t.subtrees := by
  cases t <;> simp

/-- The categories are those at the roots of the subtrees. -/
theorem map_cat_subtrees (t : Tree C W) : t.subtrees.map cat = t.cats := by
  induction t with
  | node c cs ih =>
    simp only [subtrees_node, List.map_cons, cat, cats_node, List.flatMap_def, List.map_flatten,
      List.map_map]
    exact congrArg _ (congrArg _ (List.map_congr_left ih))
  | bind n c t ih => rw [subtrees_bind, List.map_cons, cat, ih, cats_bind]
  | _ => rfl

/-! ### Free traces -/

/-- The indices of the traces free in a tree: every trace index, less those a dominating binder
of the same index binds. -/
def freeIndices : Tree C W → Finset ℕ :=
  fold (fun _ _ => ∅) (fun _ => List.foldr (· ∪ ·) ∅) (fun n _ => {n}) fun n _ s => s.erase n

@[simp] theorem freeIndices_terminal (c : C) (w : W) : (terminal c w).freeIndices = ∅ := rfl

theorem freeIndices_node (c : C) (cs : List (Tree C W)) :
    (node c cs).freeIndices = (cs.map freeIndices).foldr (· ∪ ·) ∅ := by
  simp only [freeIndices, fold_node]

@[simp] theorem freeIndices_trace (n : ℕ) (c : C) : (trace n c : Tree C W).freeIndices = {n} :=
  rfl

@[simp] theorem freeIndices_bind (n : ℕ) (c : C) (t : Tree C W) :
    (bind n c t).freeIndices = t.freeIndices.erase n := rfl

@[simp] theorem mem_freeIndices_node {i : ℕ} {c : C} {cs : List (Tree C W)} :
    i ∈ (node c cs).freeIndices ↔ ∃ t ∈ cs, i ∈ t.freeIndices := by
  rw [freeIndices_node]
  induction cs with
  | nil => simp
  | cons t ts ih => simp [ih]

/-- A tree is closed when no trace is free in it. -/
def Closed (t : Tree C W) : Prop := t.freeIndices = ∅

instance (t : Tree C W) : Decidable t.Closed := inferInstanceAs (Decidable (_ = _))

/-! ### Word substitution -/

/-- Replace the word `w` by `w'` at every terminal of category `c`. -/
def leafSubst [DecidableEq C] [DecidableEq W] (w w' : W) (c : C) : Tree C W → Tree C W :=
  fold (fun c' v => .terminal c' (if c = c' ∧ v = w then w' else v)) .node .trace .bind

section LeafSubst

variable [DecidableEq C] [DecidableEq W] (w w' : W) (c : C)

@[simp] theorem leafSubst_terminal (c' : C) (v : W) :
    leafSubst w w' c (.terminal c' v) = .terminal c' (if c = c' ∧ v = w then w' else v) := rfl

@[simp] theorem leafSubst_node (c' : C) (cs : List (Tree C W)) :
    leafSubst w w' c (.node c' cs) = .node c' (cs.map (leafSubst w w' c)) := by
  simp only [leafSubst, fold_node]

@[simp] theorem leafSubst_trace (n : ℕ) (c' : C) :
    leafSubst w w' c (.trace n c') = .trace n c' := rfl

@[simp] theorem leafSubst_bind (n : ℕ) (c' : C) (t : Tree C W) :
    leafSubst w w' c (.bind n c' t) = .bind n c' (leafSubst w w' c t) := rfl

end LeafSubst

/-! ### Positions

Through the `Branching` instance a tree takes Gorn addresses (`Branching.subtreeAt`), the
dominance order on its positions (`Branching.toTreeOrder`) and the command relations over it.
-/

open Core.Order

instance : Branching (Tree C W) where
  children
    | .terminal _ _ => []
    | .node _ cs => cs
    | .trace _ _ => []
    | .bind _ _ t => [t]

@[simp] theorem children_terminal (c : C) (w : W) : Branching.children (terminal c w) = [] := rfl

@[simp] theorem children_node (c : C) (cs : List (Tree C W)) :
    Branching.children (node c cs) = cs := rfl

@[simp] theorem children_trace (n : ℕ) (c : C) : Branching.children (trace n c : Tree C W) = [] :=
  rfl

@[simp] theorem children_bind (n : ℕ) (c : C) (t : Tree C W) :
    Branching.children (bind n c t) = [t] := rfl

end Tree

end Syntax
