import Linglib.Core.Order.TreePath
import Linglib.Core.Order.Tree
import Linglib.Core.Order.Command
import Mathlib.Algebra.Free
import Mathlib.Util.CompileInductive

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
the `IsFiniteBranching` mixin below, a `Prop`-valued well-foundedness
assertion on the child relation (mathlib idiom: structure-bearing
class + `Is…` Prop mixin, like `RootedTree` + `IsPredArchimedean`).

Known instance candidates across the library (2026-06-06 audit):
`Syntax.Tree` (constituency), `NanoTree` (Nanosyntax features),
`CFGTree` (CFG derivations — `subtreeAt` is classical Gorn
addressing), `RoseTree` (Hopf-algebra
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

/-- Membership characterization for non-root positions: descend one
child, then recurse. -/
theorem mem_validPaths_cons {t : T} {i : Nat} {rest : List Nat} :
    (⟨i :: rest⟩ : TreePath) ∈ validPaths t ↔
    ∃ c, (children t)[i]? = some c ∧ (⟨rest⟩ : TreePath) ∈ validPaths c := by
  simp only [validPaths, Set.mem_setOf_eq, subtreeAt_cons]
  rcases hmem : (children t)[i]? with _ | c <;> simp

/-- Valid paths are closed under prefixes (ancestors of a position are
positions): the set of positions is downward closed, hence inherits
the rooted-tree order stack from `TreePath`. -/
theorem validPaths_prefix_closed {t : T} {p q : TreePath}
    (hq : q ∈ validPaths t) (hpq : p ≤ q) : p ∈ validPaths t := by
  obtain ⟨s, hs⟩ := hpq
  simp only [validPaths, Set.mem_setOf_eq] at hq ⊢
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

/-! ### `IsFiniteBranching`: the well-foundedness mixin

`Prop`-valued mixin asserting that `Branching.IsChild` is well-founded
on `T` — i.e. every descent chain is finite. Unlocks carrier recursion
(`size`, `subtrees`, `yield`, `inductionOn`) via `WellFounded.fix`.

Mathlib idiom: structure-bearing class (`Branching`) + `Is…` Prop
mixin asserting a property (`IsFiniteBranching`), like `PartialOrder`
+ `IsPredArchimedean` in `RootedTree`. The mixin is `Prop` so
instances are never `noncomputable`; concrete inductives discharge it
via `Subrelation.wf` against the auto-derived `sizeOf` well-founded
relation (one-liner per instance). Carriers without auto-`SizeOf`
(e.g. `FreeMagma`, whose `genSizeOfSpec` is `false`) discharge via
`Acc.intro` + the carrier's recursor.

Previously this was a data class carrying `measure : T → Nat`, but
that design forced `noncomputable` on inductive instances (LCNF crash
on nested-`List` recursors) and broke equation-theorem elaboration
for downstream WF defs. The redesign — `Prop` mixin +
`compile_inductive%` at inductive definition sites — fixes both. -/

/-- A `Branching` carrier whose "is a child of" relation is well-founded
— i.e. every descent chain ends. Unlocks carrier recursion. -/
class IsFiniteBranching (T : Type*) [Branching T] : Prop where
  wf : WellFounded (Branching.IsChild : T → T → Prop)

/-- Build `IsFiniteBranching T` from any `Nat`-valued measure that
children strictly decrease (canonically `sizeOf` for inductives). -/
theorem IsFiniteBranching.ofMeasure {T : Type*} [Branching T] (m : T → Nat)
    (h : ∀ {c t : T}, c ∈ Branching.children t → m c < m t) :
    IsFiniteBranching T :=
  ⟨⟨fun t => by
    suffices aux : ∀ n, ∀ t, m t = n → Acc (Branching.IsChild) t by exact aux _ t rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht
      refine .intro _ (fun c hc => ?_)
      exact ih (m c) (ht ▸ h hc) c rfl⟩⟩

namespace Branching

variable {T : Type*} [Branching T] [IsFiniteBranching T]

/-- Number of nodes. -/
def size (t : T) : Nat :=
  IsFiniteBranching.wf.fix (fun t ih => 1 + ((children t).attach.map
    (fun ⟨c, hc⟩ => ih c hc)).sum) t

/-- One-step unfolding of `size`. Proved by `WellFounded.fix_eq`. -/
theorem size_eq (t : T) :
    size t = 1 + ((children t).attach.map (fun ⟨c, _⟩ => size c)).sum :=
  IsFiniteBranching.wf.fix_eq _ t

/-- Attach-free unfolding of `size`, for concrete computation. -/
theorem size_def (t : T) :
    size t = 1 + ((children t).map size).sum := by
  rw [size_eq, List.attach_map_val]

/-- All subtrees including self, pre-order. -/
def subtrees (t : T) : List T :=
  IsFiniteBranching.wf.fix (fun t ih =>
    t :: (children t).attach.flatMap (fun ⟨c, hc⟩ => ih c hc)) t

theorem subtrees_eq (t : T) :
    subtrees t = t :: (children t).attach.flatMap (fun ⟨c, _⟩ => subtrees c) :=
  IsFiniteBranching.wf.fix_eq _ t

/-- Attach-free unfolding of `subtrees`, for concrete computation. -/
theorem subtrees_def (t : T) :
    subtrees t = t :: (children t).flatMap subtrees := by
  rw [subtrees_eq]
  simp [List.flatMap_def]

theorem self_mem_subtrees (t : T) : t ∈ subtrees t := by
  rw [subtrees_eq]; exact List.mem_cons_self ..

/-- Strong induction over an `IsFiniteBranching` carrier: prove
`motive t` from `motive` on all children. Canonical mathlib pattern —
delegates to `WellFounded.fix`. -/
@[elab_as_elim]
def inductionOn {motive : T → Sort*} (t : T)
    (ih : ∀ t, (∀ c, c ∈ children t → motive c) → motive t) : motive t :=
  IsFiniteBranching.wf.fix (fun t IH => ih t fun c hc => IH c hc) t

theorem inductionOn_eq {motive : T → Sort*} (t : T)
    (ih : ∀ t, (∀ c, c ∈ children t → motive c) → motive t) :
    inductionOn t ih = ih t (fun c _ => inductionOn c ih) :=
  IsFiniteBranching.wf.fix_eq _ t

end Branching

/-! ### `HasContent` and yield

Separate class because not every rose-tree carrier has terminal
content (Nanosyntax trees carry features on every node; CFG derivation
trees distinguish terminal from nonterminal types). -/

/-- Carriers whose nodes may carry pronounceable terminal content.
`W` is an `outParam`: in linguistics use each carrier has one content
reading. (Multi-content scenarios — phonological vs orthographic — can
be supported via different wrapper types if needed.) -/
class HasContent (T : Type*) (W : outParam Type*) where
  /-- Terminal content, if any. -/
  content? : T → Option W

export HasContent (content?)

namespace Branching

variable {T W : Type*} [Branching T] [IsFiniteBranching T] [HasContent T W]

/-- Terminal yield, left to right: the frontier string. The most basic
tree-to-string map — linear precedence lives over it. -/
def yield (t : T) : List W :=
  IsFiniteBranching.wf.fix (fun t ih =>
    (content? t).toList ++
      (children t).attach.flatMap (fun ⟨c, hc⟩ => ih c hc)) t

theorem yield_eq (t : T) :
    yield t = (content? t).toList ++
      (children t).attach.flatMap (fun ⟨c, _⟩ => yield c) :=
  IsFiniteBranching.wf.fix_eq _ t

/-- Attach-free unfolding of `yield`, for concrete computation. -/
theorem yield_def (t : T) :
    yield t = (content? t).toList ++ (children t).flatMap yield := by
  rw [yield_eq]
  simp [List.flatMap_def]

/-! ### Yield with positions — the precedence-is-yield-order substrate

`yieldWithPaths` pairs each terminal with its Gorn address. Defined
via `WellFounded.fix` (not Lean's WF elaborator) so its unfold lemma is
a one-liner via `WellFounded.fix_eq` — the mathlib-reviewer's escape
from the equation-compiler timeout that the earlier
`attach.zipIdx.flatMap` formulation hit. The pairwise-Precedes bridge
(`Precedes` *is* yield order, [kayne-1994] LCA-style) is a follow-up
that builds on this substrate. -/

/-- Yield with positions: each terminal paired with its Gorn address. -/
def yieldWithPaths (t : T) : List (TreePath × W) :=
  IsFiniteBranching.wf.fix (fun t ih =>
    (content? t).toList.map (⟨⊥, ·⟩) ++
    (children t).attach.zipIdx.flatMap fun ci =>
      (ih ci.1.val ci.1.property).map fun pw =>
        (⟨ci.2 :: pw.1.toList⟩, pw.2)) t

/-- One-step unfolding of `yieldWithPaths`, by `WellFounded.fix_eq` —
the lemma that the old WF-elaborator approach could not produce. -/
theorem yieldWithPaths_eq (t : T) :
    yieldWithPaths t =
      (content? t).toList.map (⟨⊥, ·⟩) ++
      (children t).attach.zipIdx.flatMap fun ci =>
        (yieldWithPaths ci.1.val).map fun pw =>
          (⟨ci.2 :: pw.1.toList⟩, pw.2) :=
  IsFiniteBranching.wf.fix_eq _ t

end Branching

/-! ### Instance: `FreeMagma`

Mathlib's free magma is the binary rose tree (bare phrase structure in
the Minimalist reading); the instance lives here because mathlib types
take their instances in the class's home file. `FreeMagma` is declared
with `set_option genSizeOfSpec false`, so `IsFiniteBranching` cannot
use the `sizeOf` shortcut — but the inductive recursor `FreeMagma.recOnMul`
suffices for a direct `Acc.intro` proof. -/

instance {α : Type*} : Branching (FreeMagma α) where
  children
    | .of _ => []
    | .mul l r => [l, r]

@[simp] theorem freeMagma_children_of {α : Type*} (a : α) :
    Branching.children (FreeMagma.of a) = [] := rfl

@[simp] theorem freeMagma_children_mul {α : Type*} (l r : FreeMagma α) :
    Branching.children (l.mul r) = [l, r] := rfl

instance {α : Type*} : IsFiniteBranching (FreeMagma α) where
  wf := ⟨FreeMagma.rec
    (fun _ => .intro _ (fun c hc => by
      simp [Branching.IsChild, Branching.children] at hc))
    (fun _ _ ihl ihr => .intro _ (fun c hc => by
      simp only [Branching.IsChild, Branching.children, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ihl
      · exact ihr))⟩

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
instance : DecidableLE TreePath := fun p q =>
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
  simp only [commandRelation, upperBounds, TreeOrder.properDom, Set.mem_setOf_eq]
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

/-! ### Computability sentinels

`Branching.size`/`yield` on `FreeMagma` reduce by `decide` at concrete
data — protecting against `noncomputable`-regressions during refactors. -/

example : Branching.size (FreeMagma.of (1 : ℕ)) = 1 := by
  rw [Branching.size_def]; rfl

end Core.Order
