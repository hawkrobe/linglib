module

public import Linglib.Core.Data.RoseTree.Basic
public import Linglib.Core.Data.Multiset.Rel
public import Linglib.Core.Data.RoseTree.Perm
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.MapFold

/-!
# Unordered rooted trees

An unordered rooted tree with vertices labelled in `α` is a `RoseTree α` modulo the permutation
of children at every vertex: the quotient `UnorderedTree α := Quotient RoseTree.isSetoid`. In the
Connes–Kreimer literature these are the rooted trees and the ordered ones the planar rooted
trees ([foissy-introduction-hopf-algebras-trees]); [marcolli-chomsky-berwick-2025] §1.1.3 builds
syntactic objects on them, since Merge is set formation and `{α, {β, γ}}` has no order. The
identity criterion is `RoseTree.Perm` (`Core/Data/RoseTree/Perm.lean`); this file owns the
quotient: the projection `mk`, the lifting API, the lifted invariants, and the constructor `node`
on `Multiset` children, under which the grafting `B⁺` of a multiset of trees is well defined.

## Main definitions

* `UnorderedTree`, `UnorderedTree.mk`: the quotient and its projection; operations descend
  through `Quotient.lift` and proofs through `Quotient.inductionOn`, as for `Multiset`.
* `UnorderedTree.cons`: adjoin a tree as a further child of the root, the transport of the list
  cons on children; it is left-commutative, so `Multiset.foldr` builds the constructor
  `UnorderedTree.node` on a multiset of children computably.

## References

* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical Structure of Syntactic Merge*
  (2025)][marcolli-chomsky-berwick-2025]
* [L. Foissy, *An introduction to Hopf algebras of trees*][foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree

/-! ### The quotient type -/


/-- An unordered rooted tree with `α`-labelled vertices: the quotient of `RoseTree α` by the
    permutation of children at every vertex, `RoseTree.Perm`. -/
def UnorderedTree (α : Type*) : Type _ := Quotient (RoseTree.isSetoid : Setoid (RoseTree α))

namespace UnorderedTree

variable {α : Type*}

/-- The canonical projection from ordered to nonplanar trees. -/
def mk (t : RoseTree α) : UnorderedTree α := Quotient.mk _ t

/-- Two trees give the same nonplanar tree iff they're `RoseTree.Perm`-related. -/
theorem mk_eq_mk_iff {t s : RoseTree α} : mk t = mk s ↔ RoseTree.Perm t s :=
  Quotient.eq

/-- The quotient projection in `mk`-form, so that goals produced by `Quotient.inductionOn`
    display `mk` and the `mk`-stated lemmas rewrite. -/
@[simp] theorem quot_mk_eq_mk (t : RoseTree α) : (⟦t⟧ : UnorderedTree α) = mk t := rfl

/-! ### Smart leaf constructor + lifted counts

A leaf in `UnorderedTree α` is `mk (RoseTree.leaf a)`. `numNodes` is the
canonical first lifted invariant. -/

/-- A nonplanar leaf labeled `a`. -/
abbrev leaf (a : α) : UnorderedTree α := mk (RoseTree.leaf a)

/-- The **node count** (number of vertices) of a nonplanar tree, lifted
    from `RoseTree.numNodes` via `RoseTree.Perm`-invariance. -/
def numNodes : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.numNodes (fun _ _ h => RoseTree.numNodes_perm h)

@[simp] theorem numNodes_mk (t : RoseTree α) : (mk t).numNodes = t.numNodes := rfl

@[simp] theorem numNodes_leaf (a : α) : (leaf a : UnorderedTree α).numNodes = 1 := by simp

/-- The **leaf count** (number of childless vertices) of a nonplanar tree,
    lifted from `RoseTree.numLeaves` via `RoseTree.Perm`-invariance. MCB's
    complexity grading `#L` (Def. 1.6.2) is built on this. -/
def numLeaves : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.numLeaves (fun _ _ h => RoseTree.numLeaves_perm h)

@[simp] theorem numLeaves_mk (t : RoseTree α) : (mk t).numLeaves = t.numLeaves := rfl

@[simp] theorem numLeaves_leaf (a : α) : (leaf a : UnorderedTree α).numLeaves = 1 := by
  simp

/-- The **arity** (root child count) of a nonplanar tree. -/
def arity : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.arity (fun _ _ h => RoseTree.arity_perm h)

@[simp] theorem arity_mk (t : RoseTree α) : (mk t).arity = t.arity := rfl

@[simp] theorem arity_leaf (a : α) : (leaf a : UnorderedTree α).arity = 0 := rfl

/-- The **height** (number of vertices on a longest root-to-leaf path) of a nonplanar tree. -/
def height : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.height (fun _ _ h => RoseTree.height_perm h)

@[simp] theorem height_mk (t : RoseTree α) : (mk t).height = t.height := rfl

@[simp] theorem height_leaf (a : α) : (leaf a : UnorderedTree α).height = 1 := by simp

/-! ### Destructors and node injectivity

The root value and the children (as a multiset of nonplanar trees) are
`RoseTree.Perm`-invariant, so they descend to `UnorderedTree`. `congrArg` on these destructors
inverts `mk`-equality at a node with no induction, giving the injectivity
characterization `mk_node_eq_mk_node_iff`. -/

/-- The root value of a nonplanar tree. -/
def value : UnorderedTree α → α :=
  Quotient.lift RoseTree.value (fun _ _ h => h.value_eq)

@[simp] theorem value_mk (t : RoseTree α) : (mk t).value = t.value := rfl

/-- The mk-image of the root children, as a multiset, is a `RoseTree.Perm`-invariant:
    `Perm.children_rel` collapses under `mk`. -/
theorem perm_children_map_mk {t s : RoseTree α} (h : RoseTree.Perm t s) :
    (↑(t.children.map mk) : Multiset (UnorderedTree α)) = ↑(s.children.map mk) := by
  rw [← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.rel_eq, Multiset.rel_map]
  exact h.children_rel.mono fun _ _ _ _ => mk_eq_mk_iff.mpr

/-- The children of a nonplanar tree, as a multiset of nonplanar trees. -/
def children : UnorderedTree α → Multiset (UnorderedTree α) :=
  Quotient.lift (fun t => ↑(t.children.map mk)) (fun _ _ h => perm_children_map_mk h)

@[simp] theorem children_mk (t : RoseTree α) :
    (mk t).children = ↑(t.children.map mk) := rfl

/-- Injectivity of the node constructor on the quotient: `mk`-images of two nodes are
    equal iff the root values agree and the children agree as multisets of nonplanar
    trees. The forward direction is `congrArg` on the `value` and `children`
    destructors; the backward direction assembles a `RoseTree.Perm` componentwise. -/
theorem mk_node_eq_mk_node_iff {a b : α} {cs ds : List (RoseTree α)} :
    mk (.node a cs) = mk (.node b ds) ↔
      a = b ∧ (↑(cs.map mk) : Multiset (UnorderedTree α)) = ↑(ds.map mk) := by
  constructor
  · intro h
    exact ⟨by simpa [RoseTree.value] using congrArg value h,
           by simpa [RoseTree.children] using congrArg children h⟩
  · rintro ⟨rfl, hc⟩
    rw [← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.rel_eq, Multiset.rel_map] at hc
    obtain ⟨ds', hf, hperm⟩ := Multiset.rel_coe_iff_exists.mp
      (hc.mono fun x _ y _ h => mk_eq_mk_iff.mp h)
    exact mk_eq_mk_iff.mpr ((RoseTree.Perm.node_of_forall₂ hf).trans
      (RoseTree.Perm.node_of_perm hperm))

/-! ### Adjoining a child, and the node constructor

`cons c t` adjoins `c` as a further child of the root of `t`; it is the transport of the list
cons on children lists and is left-commutative, so `node a F` is its `Multiset.foldr` over the
children `F` starting from the leaf `a`. Both are computable, and `node_mk_tree_list` reads
`node` back on a list of planar children. -/

/-- Adjoin a tree as a further child of the root. -/
def cons (c t : UnorderedTree α) : UnorderedTree α :=
  Quotient.liftOn₂ c t (fun c t => mk (.node t.value (c :: t.children))) fun _ _ _ _ hc ht =>
    mk_eq_mk_iff.mpr (perm_node_iff.mpr ⟨ht.value_eq, by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe]
      exact ht.children_rel.cons hc⟩)

@[simp] theorem cons_mk (c : RoseTree α) (a : α) (cs : List (RoseTree α)) :
    cons (mk c) (mk (.node a cs)) = mk (.node a (c :: cs)) := rfl

instance : LeftCommutative (cons (α := α)) :=
  ⟨fun c d t => Quotient.inductionOn₃ c d t fun _ _ t => by
    obtain ⟨a, cs⟩ := t
    exact mk_eq_mk_iff.mpr (.node (.swap ..))⟩

/-- Build an unordered tree from a label and a multiset of children, by adjoining the children
    one at a time to the leaf. -/
def node (a : α) (F : Multiset (UnorderedTree α)) : UnorderedTree α := F.foldr cons (leaf a)

/-- The empty-forest node is the leaf. -/
@[simp] theorem node_zero (a : α) : node a (0 : Multiset (UnorderedTree α)) = leaf a := rfl

theorem node_cons (a : α) (c : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    node a (c ::ₘ F) = cons c (node a F) :=
  Multiset.foldr_cons ..

@[simp] theorem cons_node (a : α) (c : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    cons c (node a F) = node a (c ::ₘ F) :=
  (node_cons a c F).symm

/-- `node` on the `mk`-image of a list of planar children is `mk` of the planar node. -/
theorem node_mk_tree_list (a : α) (ps : List (RoseTree α)) :
    node a (Multiset.ofList (ps.map mk)) = mk (.node a ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.map_cons, ← Multiset.cons_coe, node_cons, ih]; rfl

/-- Binary case of `node_mk_tree_list`: a bare pair of `mk`-lifted trees. -/
theorem node_pair_mk (a : α) (p q : RoseTree α) :
    node a {mk p, mk q} = mk (.node a [p, q]) :=
  node_mk_tree_list a [p, q]

/-- Choose planar representatives for a whole forest at once: every
    `Multiset (UnorderedTree α)` is the `mk`-image of a list of planar trees. Descent
    proofs that use this eliminator meet `node_mk_tree_list` on the nose, with no
    `Quotient.out` repair. -/
@[elab_as_elim]
theorem forest_inductionOn {motive : Multiset (UnorderedTree α) → Prop}
    (F : Multiset (UnorderedTree α))
    (h : ∀ cs : List (RoseTree α), motive (Multiset.ofList (cs.map mk))) : motive F := by
  refine Quotient.inductionOn F fun lst => ?_
  have hrep : (lst.map Quotient.out).map mk = lst := by
    rw [List.map_map]
    exact (List.map_congr_left fun x _ => x.out_eq).trans (List.map_id lst)
  exact hrep ▸ h (lst.map Quotient.out)

/-! ### The destructors of a `node` -/

@[simp] theorem value_node (a : α) (F : Multiset (UnorderedTree α)) : value (node a F) = a := by
  induction F using forest_inductionOn with
  | h ps => rw [node_mk_tree_list]; rfl

@[simp] theorem children_node (a : α) (F : Multiset (UnorderedTree α)) :
    children (node a F) = F := by
  induction F using forest_inductionOn with
  | h ps => rw [node_mk_tree_list]; rfl

/-- Eta law: every tree is the `node` of its root value and children. -/
theorem node_eta (t : UnorderedTree α) : node (value t) (children t) = t := by
  induction t using Quotient.inductionOn with
  | h p =>
    cases p with
    | node a cs => exact node_mk_tree_list a cs

/-! ### Node count of a `node` -/

/-- Every tree has at least one vertex (the root). -/
theorem numNodes_pos (t : UnorderedTree α) : 0 < t.numNodes := by
  induction t using Quotient.inductionOn with
  | h p => exact RoseTree.numNodes_pos p

/-- Node count of a smart-constructor `node`: one (the root) plus the
    total node count of the children multiset. -/
@[simp] theorem numNodes_node (a : α) (F : Multiset (UnorderedTree α)) :
    (node a F).numNodes = (F.map numNodes).sum + 1 := by
  induction F using forest_inductionOn with
  | h ps =>
    rw [node_mk_tree_list, numNodes_mk, RoseTree.numNodes_node, Multiset.map_coe,
      Multiset.sum_coe, List.map_map]
    rfl

/-! ### Height of a `node` -/

/-- A tree's height is strictly less than the height of any node containing
    it as a child. -/
theorem height_lt_of_mem (T : UnorderedTree α) (F : Multiset (UnorderedTree α))
    (hT : T ∈ F) (a : α) : T.height < (node a F).height := by
  revert hT
  induction F using forest_inductionOn with
  | h ps =>
    intro hT
    rw [node_mk_tree_list]
    rw [show (Multiset.ofList (ps.map mk) : Multiset (UnorderedTree α)) =
          ((ps.map mk : List (UnorderedTree α)) : Multiset _) from rfl,
        Multiset.mem_coe, List.mem_map] at hT
    obtain ⟨c, hc, rfl⟩ := hT
    exact RoseTree.height_lt_of_mem (t := RoseTree.node a ps) hc

end UnorderedTree


namespace UnorderedTree

variable {α β γ : Type*}

/-! ## Functoriality

Lift `RoseTree.map` through the quotient. Counterpart of `List.map` for
lists: a function `f : α → β` lifts to `UnorderedTree α → UnorderedTree β` by
relabeling every vertex. -/

/-- Map a function over the vertex labels of a nonplanar rooted tree.
    Lifted from `RoseTree.map` via `Quotient.map`. -/
def map (f : α → β) : UnorderedTree α → UnorderedTree β :=
  Quotient.map (RoseTree.map f)
    (fun _ _ h => RoseTree.Perm.map f h)

/-- Quotient-unfolding for `UnorderedTree.map`. Plain lemma (not `@[simp]`)
    since mathlib's generic `Quotient.map_mk` covers the same ground. -/
theorem map_mk (f : α → β) (t : RoseTree α) :
    map f (mk t) = mk (RoseTree.map f t) := rfl

theorem map_leaf (f : α → β) (a : α) :
    map f (leaf a) = leaf (f a) := by
  show map f (mk (RoseTree.leaf a)) = mk (RoseTree.leaf (f a))
  rw [map_mk, RoseTree.map_leaf]

@[simp] theorem map_id (t : UnorderedTree α) : map id t = t := by
  refine Quotient.inductionOn t ?_
  intro p
  show map id (mk p) = mk p
  rw [map_mk, RoseTree.id_map]

theorem map_map (f : α → β) (g : β → γ) (t : UnorderedTree α) :
    map g (map f t) = map (g ∘ f) t := by
  refine Quotient.inductionOn t ?_
  intro p
  show map g (map f (mk p)) = map (g ∘ f) (mk p)
  rw [map_mk, map_mk, map_mk, RoseTree.comp_map]

/-- `map` commutes with `node`: relabel the root and map the children. -/
theorem map_node (f : α → β) (a : α) (cs : Multiset (UnorderedTree α)) :
    map f (node a cs) = node (f a) (cs.map (map f)) := by
  refine forest_inductionOn cs fun ps => ?_
  rw [node_mk_tree_list, map_mk, RoseTree.map_node,
    show (Multiset.ofList (ps.map mk)).map (map f)
        = Multiset.ofList ((ps.map (RoseTree.map f)).map mk) by
      simp [List.map_map, Function.comp_def, map_mk],
    node_mk_tree_list]

/-! ### Counting interactions -/

@[simp] theorem numNodes_map (f : α → β) (t : UnorderedTree α) :
    (map f t).numNodes = t.numNodes := by
  refine Quotient.inductionOn t ?_
  intro p
  show (map f (mk p)).numNodes = (mk p).numNodes
  rw [map_mk, numNodes_mk, numNodes_mk, RoseTree.numNodes_map]

@[simp] theorem height_map (f : α → β) (t : UnorderedTree α) :
    (map f t).height = t.height := by
  refine Quotient.inductionOn t ?_
  intro p
  show (map f (mk p)).height = (mk p).height
  rw [map_mk, height_mk, height_mk, RoseTree.height_map]

@[simp] theorem arity_map (f : α → β) (t : UnorderedTree α) :
    (map f t).arity = t.arity := by
  refine Quotient.inductionOn t ?_
  intro p
  show (map f (mk p)).arity = (mk p).arity
  rw [map_mk, arity_mk, arity_mk, RoseTree.arity_map]

@[simp] theorem numLeaves_map (f : α → β) (t : UnorderedTree α) :
    (map f t).numLeaves = t.numLeaves := by
  refine Quotient.inductionOn t ?_
  intro p
  show (map f (mk p)).numLeaves = (mk p).numLeaves
  rw [map_mk, numLeaves_mk, numLeaves_mk, RoseTree.numLeaves_map]

end UnorderedTree
