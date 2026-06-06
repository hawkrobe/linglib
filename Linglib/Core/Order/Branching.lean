import Linglib.Core.Order.TreePath
import Linglib.Core.Order.Tree

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

**No well-foundedness is required here.** The path machinery recurses
on the *path* (structurally decreasing `List Nat`), not on `T`, so
this class is law-free on the carrier and still theorem-rich; carriers
with infinite depth are admissible. Recursion *on the carrier* (size,
subtree enumeration, yield) needs the `FiniteBranching` mixin (future
work, phase 2).

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

end Core.Order
