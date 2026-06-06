import Linglib.Core.Order.TreePath
import Linglib.Core.Order.Tree
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

**No well-foundedness is required for the base class.** The path
machinery recurses on the *path* (structurally decreasing `List Nat`),
not on `T`, so `Branching` is law-free on the carrier and still
theorem-rich; carriers with infinite depth are admissible. Recursion
*on the carrier* (`size`, `subtrees`, `yield`, `inductionOn`) needs
the `FiniteBranching` mixin below, whose one law — children strictly
decrease `sizeOf` — concrete inductives discharge by `cases` + `omega`.

Known instance candidates across the library (2026-06-06 audit):
`Syntax.Tree` (constituency), `NanoTree` (Nanosyntax features),
`CFGTree` (CFG derivations — `subtreeAt` is classical Gorn
addressing), `Core.Combinatorics.RootedTree.Planar` (Hopf-algebra
trees), `FreeMagma` (bare phrase structure), Dependency-Grammar
positions.
-/

namespace Core.Order

/-- Rose-tree interface: a carrier with an ordered list of children.
`[]` for leaves. See the module docstring for what one field buys. -/
class Branching (T : Type*) where
  /-- Ordered children. -/
  children : T → List T

namespace Branching

variable {T : Type*} [Branching T]

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

/-- Valid paths are closed under prefixes (ancestors of a position are
positions): the set of positions is downward closed, hence inherits
the rooted-tree order stack from `TreePath`. -/
theorem validPaths_prefix_closed {t : T} {p q : TreePath}
    (hq : q ∈ validPaths t) (hpq : p ≤ q) : p ∈ validPaths t := by
  obtain ⟨s, hs⟩ := hpq
  simp only [validPaths, Set.mem_setOf_eq] at hq ⊢
  -- `subtreeAt t (p.toList ++ s)` factors through `subtreeAt t p.toList`.
  suffices h : ∀ (l₁ l₂ : List Nat) (t : T),
      (subtreeAt t (l₁ ++ l₂)).isSome → (subtreeAt t l₁).isSome by
    exact h p.toList s t (by rw [hs]; exact hq)
  intro l₁
  induction l₁ with
  | nil => intro _ _ _; simp
  | cons i rest ih =>
    intro l₂ t h
    rw [List.cons_append, subtreeAt_cons] at h
    rw [subtreeAt_cons]
    rcases hmem : (children t)[i]? with _ | c
    · rw [hmem] at h
      simp at h
    · rw [hmem] at h
      exact ih l₂ c h

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

/-! ### `FiniteBranching`: the recursion mixin

Recursion *on the carrier* (size, subtree enumeration, yield,
induction) is not definable from `Branching` alone: Lean cannot see
structural decrease through a class field. The mixin supplies the
missing law — children strictly decrease `sizeOf` — which concrete
inductive carriers discharge by `cases` + `omega` over their
auto-derived `SizeOf`. -/

/-- A `Branching` carrier whose children strictly decrease `sizeOf`.
Unlocks carrier recursion: `size`, `subtrees`, `yield`, `inductionOn`. -/
class FiniteBranching (T : Type*) [SizeOf T] extends Branching T where
  /-- Children are `sizeOf`-smaller than their parent. -/
  sizeOf_children : ∀ {c t : T}, c ∈ Branching.children t → sizeOf c < sizeOf t

namespace Branching

variable {T : Type*} [SizeOf T] [FiniteBranching T]

/-- Number of nodes. -/
def size (t : T) : Nat :=
  1 + ((children t).attach.map (fun ⟨c, hc⟩ => size c)).sum
termination_by sizeOf t
decreasing_by exact FiniteBranching.sizeOf_children hc

/-- Attach-free unfolding of `size`, for concrete computation. -/
theorem size_def (t : T) :
    size t = 1 + ((children t).map size).sum := by
  rw [size, List.attach_map_val]

/-- All subtrees including self, pre-order. -/
def subtrees (t : T) : List T :=
  t :: (children t).attach.flatMap (fun ⟨c, hc⟩ => subtrees c)
termination_by sizeOf t
decreasing_by exact FiniteBranching.sizeOf_children hc

/-- Attach-free unfolding of `subtrees`, for concrete computation. -/
theorem subtrees_def (t : T) :
    subtrees t = t :: (children t).flatMap subtrees := by
  rw [subtrees]
  simp [List.flatMap_def]

theorem self_mem_subtrees (t : T) : t ∈ subtrees t := by
  rw [subtrees]; exact List.mem_cons_self ..

/-- Strong induction over a `FiniteBranching` carrier: prove `motive t`
from `motive` on all children. -/
theorem inductionOn {motive : T → Prop} (t : T)
    (ih : ∀ t, (∀ c ∈ children t, motive c) → motive t) : motive t := by
  induction ht : sizeOf t using Nat.strong_induction_on generalizing t with
  | _ n ihn =>
    subst ht
    exact ih t fun c hc =>
      ihn (sizeOf c) (FiniteBranching.sizeOf_children hc) c rfl

end Branching

/-! ### `HasContent` and yield

Separate class because not every rose-tree carrier has terminal
content (Nanosyntax trees carry features on every node; CFG derivation
trees distinguish terminal from nonterminal types). -/

/-- Carriers whose nodes may carry pronounceable terminal content. -/
class HasContent (T : Type*) (W : outParam Type*) where
  /-- Terminal content, if any. -/
  content? : T → Option W

export HasContent (content?)

namespace Branching

variable {T W : Type*} [SizeOf T] [FiniteBranching T] [HasContent T W]

/-- Terminal yield, left to right: the frontier string. The most basic
tree-to-string map — linear precedence lives over it. -/
def yield (t : T) : List W :=
  (content? t).toList ++ (children t).attach.flatMap (fun ⟨c, hc⟩ => yield c)
termination_by sizeOf t
decreasing_by exact FiniteBranching.sizeOf_children hc

/-- Attach-free unfolding of `yield`, for concrete computation. -/
theorem yield_def (t : T) :
    yield t = (content? t).toList ++ (children t).flatMap yield := by
  rw [yield]
  simp [List.flatMap_def]

end Branching

/-! ### Instance: `FreeMagma`

Mathlib's free magma is the binary rose tree (bare phrase structure in
the Minimalist reading); the instance lives here because mathlib types
take their instances in the class's home file. The bespoke
`FreeMagma.toTree` bridge in `Syntax/Tree/Basic.lean` becomes one of
two routes to the position machinery — this instance is the direct one. -/

instance {α : Type*} : Branching (FreeMagma α) where
  children
    | .of _ => []
    | .mul l r => [l, r]

instance {α : Type*} : FiniteBranching (FreeMagma α) where
  sizeOf_children {c t} hc := by
    cases t with
    | of _ => simp [Branching.children] at hc
    | mul l r =>
      simp only [Branching.children, List.mem_cons, List.not_mem_nil, or_false] at hc
      have hmul : sizeOf (FreeMagma.mul l r) = 1 + sizeOf l + sizeOf r := rfl
      rcases hc with rfl | rfl <;> omega

end Core.Order
