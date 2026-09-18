import Linglib.Core.Order.TreePath
import Linglib.Core.Order.Tree
import Linglib.Core.Order.Command
import Mathlib.Algebra.Free

/-!
# `Branching`: the rose-tree interface

A carrier `T` is `Branching` when each value exposes an **ordered list
of children**. One field derives, for every instance:

* Gorn-address machinery: `subtreeAt`, `validPaths`, `daughters`
* the dominance order on positions (`toTreeOrder`), unlocking the
  [barker-pullum-1990] command-relation library
  (`Core/Order/Command.lean`)
* via `Core/Order/TreePath.lean`, mathlib's rooted-tree order stack on
  positions: root (`⊥`), parent (`Order.pred`), least common ancestor
  (`⊓`), finite ancestor chains.

Sibling order (the `List`) is the load-bearing choice: linear
precedence and planarity are real structure that mathlib's
`Quiver`/`Digraph`/`SimpleGraph` forget, so those are forgetful shadows
of this class, not its basis.

No well-foundedness is required: the path machinery recurses on the
*path* (a structurally decreasing `List ℕ`), not on `T`, so the class is
law-free on the carrier and carriers of infinite depth are admissible.
-/

namespace Core.Order

/-- Rose-tree interface: a carrier with an ordered list of children.
`[]` for leaves. See the module docstring for what one field buys. -/
class Branching (T : Type*) where
  /-- Ordered children. -/
  children : T → List T

namespace Branching

variable {T : Type*} [Branching T]

/-- The "is a child of" relation on a `Branching` carrier. -/
def IsChild (c t : T) : Prop := c ∈ children t

/-- Daughters of a node — `children`, by its linguistic name. -/
abbrev daughters (t : T) : List T := children t

/-- Subtree at a Gorn address; `none` if the path leaves the tree.
Recursion is on the path, so no well-foundedness on `T` is needed. -/
def subtreeAt (t : T) : List Nat → Option T
  | [] => some t
  | i :: rest => ((children t)[i]?).bind fun c => subtreeAt c rest

@[simp] theorem subtreeAt_nil (t : T) : subtreeAt t [] = some t := rfl

@[simp] theorem subtreeAt_cons (t : T) (i : Nat) (rest : List Nat) :
    subtreeAt t (i :: rest) =
    ((children t)[i]?).bind fun c => subtreeAt c rest := rfl

/-- Valid positions of a tree. Node identity is the **position**
(`TreePath`), never the subtree value: identical subtrees occur at
multiple positions, so orders and graphs must live on paths. -/
def validPaths (t : T) : Set TreePath :=
  {p | (subtreeAt t p.toList).isSome}

theorem bot_mem_validPaths (t : T) : (⊥ : TreePath) ∈ validPaths t := by
  simp [validPaths, subtreeAt]

/-- Gorn-address composition: descending along `p ++ q` is descending
along `p`, then along `q` from there. -/
theorem subtreeAt_append (t : T) (p q : List Nat) :
    subtreeAt t (p ++ q) = (subtreeAt t p).bind (subtreeAt · q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    rw [List.cons_append, subtreeAt_cons, subtreeAt_cons]
    rcases hmem : (children t)[i]? with _ | c
    · rfl
    · exact ih c

theorem subtreeAt_cons_eq_some_iff {t s : T} {i : Nat} {p : List Nat} :
    subtreeAt t (i :: p) = some s ↔ ∃ c, (children t)[i]? = some c ∧ subtreeAt c p = some s := by
  simp [Option.bind_eq_some_iff]

/-- Every prefix of an address inside the tree is inside the tree. -/
theorem subtreeAt_take_isSome {t s : T} {p : List Nat} (h : subtreeAt t p = some s) (k : Nat) :
    (subtreeAt t (p.take k)).isSome := by
  rw [← List.take_append_drop k p, subtreeAt_append] at h
  exact Option.isSome_of_isSome_bind (by rw [h]; rfl)

/-- Membership characterization for non-root positions: descend one
child, then recurse. -/
theorem mem_validPaths_cons {t : T} {i : Nat} {rest : List Nat} :
    (⟨i :: rest⟩ : TreePath) ∈ validPaths t ↔
    ∃ c, (children t)[i]? = some c ∧ (⟨rest⟩ : TreePath) ∈ validPaths c := by
  simp only [validPaths, Set.mem_ofPred_eq, subtreeAt_cons]
  rcases hmem : (children t)[i]? with _ | c <;> simp

/-- Valid paths are closed under prefixes (ancestors of a position are
positions): the set of positions is downward closed, hence inherits
the rooted-tree order stack from `TreePath`. -/
theorem validPaths_prefix_closed {t : T} {p q : TreePath}
    (hq : q ∈ validPaths t) (hpq : p ≤ q) : p ∈ validPaths t := by
  obtain ⟨s, hs⟩ := hpq
  simp only [validPaths, Set.mem_ofPred_eq] at hq ⊢
  rw [← hs, subtreeAt_append] at hq
  exact Option.isSome_of_isSome_bind hq

/-- The dominance order of any `Branching` carrier, as a
[barker-pullum-1990] `TreeOrder` on positions. Every instance inherits
the command-relation library through this single definition —
generalizing the former `Syntax.Tree.toTreeOrder`. -/
def toTreeOrder (t : T) : TreeOrder TreePath where
  nodes := validPaths t
  root := ⊥
  root_in_nodes := bot_mem_validPaths t
  root_le_all := fun _ _ => List.nil_prefix
  ancestor_connected := fun _ _ _ h₁ h₂ => TreePath.prefix_or_prefix h₁ h₂

end Branching

/-! ### Instance: `FreeMagma`

Mathlib's free magma is the binary rose tree (bare phrase structure in
the Minimalist reading); the instance lives here because mathlib types
take their instances in the class's home file. -/

instance {α : Type*} : Branching (FreeMagma α) where
  children
    | .of _ => []
    | .mul l r => [l, r]

@[simp] theorem freeMagma_children_of {α : Type*} (a : α) :
    Branching.children (FreeMagma.of a) = [] := rfl

@[simp] theorem freeMagma_children_mul {α : Type*} (l r : FreeMagma α) :
    Branching.children (l.mul r) = [l, r] := rfl

/-! ### Decidable command relations over `toTreeOrder`

`commandRelation (toTreeOrder t) P` is decidable at concrete positions:
the dominators of `a` are exactly the prefixes of `a`'s path
(`List.inits`), a finite list, so the defining universal collapses to a
`List`-bounded one. This unlocks `decide` for c-command facts on
concrete trees ([barker-pullum-1990], [reinhart-1976]). The branching
property is supplied by `isBranchingAt` (≥ 2 children at the position),
the geometric reading of [reinhart-1976]'s "branching node". -/

namespace Branching

variable {T : Type*} [Branching T]

/-- Dominance (`p ≤ q`, prefix order) on positions is decidable. -/
instance : DecidableLE TreePath := fun _ _ =>
  decidable_of_iff _ TreePath.le_def.symm

/-- A position `p` is a **branching node** of `t` when its subtree has at
least two children — the geometric reading of [reinhart-1976]'s "first
branching node" generating relation. -/
def isBranchingAt (t : T) (p : TreePath) : Prop :=
  ∃ s, subtreeAt t p.toList = some s ∧ 2 ≤ (children s).length

instance decIsBranchingAt (t : T) (p : TreePath) : Decidable (isBranchingAt t p) :=
  match h : subtreeAt t p.toList with
  | none => isFalse (by rintro ⟨s, hs, _⟩; rw [h] at hs; simp at hs)
  | some s =>
    if hlen : 2 ≤ (children s).length then
      isTrue ⟨s, h, hlen⟩
    else
      isFalse (by rintro ⟨s', hs', hlen'⟩; rw [h] at hs'; cases hs'; exact hlen hlen')

instance (t : T) : DecidablePred (isBranchingAt t) := fun p => decIsBranchingAt t p

/-- Membership in `commandRelation (toTreeOrder t) P` collapses to a
finite universal over the proper prefixes of `a`: the only nodes that
properly dominate `a` are its proper prefixes (`a.toList.inits`). This
is the key reduction making c-command facts `decide`-able. -/
theorem mem_commandRelation_toTreeOrder_iff
    (t : T) (P : Set TreePath) (a b : TreePath) :
    (a, b) ∈ commandRelation (toTreeOrder t) P ↔
      ∀ x ∈ a.toList.inits.map TreePath.mk, x ≠ a → x ∈ P → x ≤ b := by
  simp only [commandRelation, upperBounds, TreeOrder.properDom, Set.mem_ofPred_eq]
  constructor
  · intro h x hx hne hP
    rw [List.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact h ⟨l⟩ ⟨⟨(List.mem_inits _ _).mp hl, hne⟩, hP⟩
  · intro h x ⟨⟨hxa, hne⟩, hP⟩
    refine h x ?_ hne hP
    rw [List.mem_map]
    exact ⟨x.toList, (List.mem_inits _ _).mpr (TreePath.le_def.mp hxa), rfl⟩

instance decMemCommandRelation
    (t : T) (P : Set TreePath) [DecidablePred (· ∈ P)] (a b : TreePath) :
    Decidable ((a, b) ∈ commandRelation (toTreeOrder t) P) :=
  decidable_of_iff _ (mem_commandRelation_toTreeOrder_iff t P a b).symm

instance decMemMateRelation
    (t : T) (P : Set TreePath) [DecidablePred (· ∈ P)] (ab : TreePath × TreePath) :
    Decidable (ab ∈ mateRelation (toTreeOrder t) P) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **c-command** over a concrete carrier ([reinhart-1976]'s c-command):
the [barker-pullum-1990] command relation generated by the geometric
branching nodes `isBranchingAt t`. Unlike the abstract `cCommand`
(`Core/Order/Command.lean`, parameterised by the order-theoretic
`branchingNodes`), this reads the branching property directly off the
carrier, so it is decidable and matches sister-form c-command on binary
trees. `abbrev` so membership inherits `decMemCommandRelation`. -/
abbrev cCommandAt (t : T) : Set (TreePath × TreePath) :=
  commandRelation (toTreeOrder t) {p | isBranchingAt t p}

end Branching

end Core.Order
