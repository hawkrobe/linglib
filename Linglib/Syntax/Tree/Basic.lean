import Mathlib.Data.List.Infix
import Mathlib.Algebra.Free
import Linglib.Core.Order.Branching

/-!
# Constituency Trees

The **constituency tree and LF interface format** of the Syntax layer:
one tree type, parameterized by node labels (`C`) and terminal content
(`W`), shared by the frameworks whose structures *are* constituency
trees — not by all of syntax. The library has two structural hubs:

1. **`Syntax.Tree` (this file)** — for constituency: H&K composition
   reads it (LF), Katzir structural operations transform it (PF),
   Minimalist derivations project *down* to it at Spell-Out.
2. **`Core.Order.TreeOrder` + the B&P command library** — the genuinely
   framework-agnostic layer, where non-constituency frameworks connect
   via their own node types (HPSG signs, DG word-indices, Minimalist
   syntactic objects), each with its own dominance order.

Frameworks whose structures are **not** trees do not and cannot
instantiate this type: CCG derivations are proof trees (nodes are rule
applications); HPSG signs are reentrant feature structures (structure
sharing has no tree representation); dependency structures are
head-indexed graphs; multidominance objects are nonplanar (which is why
`Syntax/Minimalist/` keeps its own `SyntacticObject` and only projects
to `Tree` at the interface).

## `Syntax.Tree C W`

N-ary branching with categories on every node. Read by both interfaces:
- **Compositional interpretation** (LF): `interp`/`evalTree`
  in `Semantics/Composition/Tree.lean` — type-driven, ignores categories
- **Structural operations** (PF): [katzir-2007] `StructOp` (substitution,
  deletion, contraction) in `Semantics/Alternatives/Structural.lean` —
  category-aware

The generic core is `terminal`/`node` with the pluggable category
parameter `C` (UD tags, feature bundles, `Unit` for unlabeled, ...).
The `trace` and `bind` constructors encode the **trace-theoretic / QR**
analysis of movement specifically ([heim-kratzer-1998] Ch. 5): indexed
traces plus λ-binders. Rival representations of movement are *not*
expressible on this type — copy theory needs a side-car chain relation
over `TreePath`s, and multidominance needs the nonplanar
`SyntacticObject` (`Syntax/Minimalist/Multidominance.lean`). Frameworks
without movement simply never construct these cases. Binder–trace
well-formedness (each `bind n` binding a matching `trace n`) is a
predicate to be imposed, not a type guarantee; `bind`'s category label
is recorded for uniformity but is not consulted by `interp` or
`StructOp`.

### Instantiations

- `Tree Unit String` — category-free, for H&K composition. Use convenience
  constructors `.leaf`, `.bin`, `.un`, `.tr`, `.binder`.
- `Tree Cat String` — UD-grounded categories (`Syntax/Tree/Cat.lean`),
  for Katzir structural alternatives.
- `Tree Unit LIToken` — bare phrase structure projected from Minimalist
  syntax at Spell-Out via `FreeMagma.toTree` (categories inside the
  token, not on nodes).

## Positions and dominance

`Tree` is an instance of `Core.Order.Branching` (the rose-tree
interface), so all position machinery is inherited rather than
re-stipulated: Gorn addresses (`Core.Order.TreePath`), the dominance
order with mathlib's rooted-tree stack (root `⊥`, parent `Order.pred`,
least common ancestor `⊓`), and the forgetful map
`Core.Order.Branching.toTreeOrder` into the B&P command-relation
library (`Linglib.Core.Order.Command`, [barker-pullum-1990]).
-/

namespace Syntax

/-! ### The tree type -/

/-- Constituency tree, parameterized by node label type `C` and terminal
word type `W`.

- `terminal c w` — leaf carrying category `c` and word `w`
- `node c cs` — internal node with category `c` and children `cs`
- `trace n c` — movement trace with index `n` and category `c`
- `bind n c body` — λ-abstraction with index `n`, category `c`, scope `body`

The `node` constructor takes a `List` of children, subsuming both
binary branching (for Heim & Kratzer composition) and n-ary structure
(for Katzir's deletion operation). Binary nodes are `node c [l, r]`.

`trace` and `bind` support Quantifier Raising and variable binding.
Frameworks without movement (CCG, HPSG) simply never construct these.

For category-free trees (`C = Unit`), use the convenience constructors
`leaf`, `bin`, `un`, `tr`, `binder` which hide the `Unit` parameter. -/
inductive Tree (C : Type*) (W : Type*) where
  | terminal : C → W → Tree C W
  | node     : C → List (Tree C W) → Tree C W
  | trace    : Nat → C → Tree C W
  | bind     : Nat → C → Tree C W → Tree C W
  deriving Repr

namespace Tree

variable {C W : Type*}

-- ── Convenience constructors for C = Unit ─────────────────────────
-- Category-free trees (for H&K composition, Minimalism, etc.) use
-- these to avoid writing `()` everywhere.

@[match_pattern] abbrev leaf (w : W) : Tree Unit W := .terminal () w
@[match_pattern] abbrev un (t : Tree Unit W) : Tree Unit W := .node () (t :: [])
@[match_pattern] abbrev bin (t1 t2 : Tree Unit W) : Tree Unit W := .node () (t1 :: t2 :: [])
@[match_pattern] abbrev tr (n : Nat) : Tree Unit W := .trace n ()
@[match_pattern] abbrev binder (n : Nat) (body : Tree Unit W) : Tree Unit W := .bind n () body

/-! ### Basic accessors -/

/-- Category label of the root node. Total: every constructor carries
a category (including `bind`, where it labels the result of PA). -/
def cat : Tree C W → C
  | .terminal c _ => c
  | .node c _ => c
  | .trace _ c => c
  | .bind _ c _ => c

/-! ### Decidable equality

`DecidableEq` is the single source of truth for tree equality; `BEq` and
`LawfulBEq (Tree C W)` come for free (and coherently) from the global
`instBEqOfDecidableEq`. A hand-rolled `beq`/`BEq` instance used to shadow
this — it left `LawfulBEq (Tree C W)` unsynthesizable and was a second,
unproven-coherent notion of tree equality, so it was removed. -/

-- ── Manual `decEq` (nested-inductive `deriving DecidableEq` fails: Lean
-- core's `mkDecEq` bails on nested inductives, `isNested → return false`) ──

mutual
  /-- Decidable equality on `Tree C W`, mutually recursive with the
  list-of-trees case. Required because `deriving DecidableEq` does not
  handle the nested `List (Tree C W)` in `node`. -/
  def decEq [DecidableEq C] [DecidableEq W] :
      (a b : Tree C W) → Decidable (a = b)
    | .terminal c₁ w₁, .terminal c₂ w₂ =>
      if hc : c₁ = c₂ then
        if hw : w₁ = w₂ then isTrue (by rw [hc, hw])
        else isFalse fun h => by cases h; exact hw rfl
      else isFalse fun h => by cases h; exact hc rfl
    | .node c₁ cs₁, .node c₂ cs₂ =>
      if hc : c₁ = c₂ then
        match decEqList cs₁ cs₂ with
        | isTrue hcs => isTrue (by rw [hc, hcs])
        | isFalse hcs => isFalse fun h => by cases h; exact hcs rfl
      else isFalse fun h => by cases h; exact hc rfl
    | .trace n₁ c₁, .trace n₂ c₂ =>
      if hn : n₁ = n₂ then
        if hc : c₁ = c₂ then isTrue (by rw [hn, hc])
        else isFalse fun h => by cases h; exact hc rfl
      else isFalse fun h => by cases h; exact hn rfl
    | .bind n₁ c₁ b₁, .bind n₂ c₂ b₂ =>
      if hn : n₁ = n₂ then
        if hc : c₁ = c₂ then
          match decEq b₁ b₂ with
          | isTrue hb => isTrue (by rw [hn, hc, hb])
          | isFalse hb => isFalse fun h => by cases h; exact hb rfl
        else isFalse fun h => by cases h; exact hc rfl
      else isFalse fun h => by cases h; exact hn rfl
    | .terminal _ _, .node _ _ => isFalse fun h => by cases h
    | .terminal _ _, .trace _ _ => isFalse fun h => by cases h
    | .terminal _ _, .bind _ _ _ => isFalse fun h => by cases h
    | .node _ _, .terminal _ _ => isFalse fun h => by cases h
    | .node _ _, .trace _ _ => isFalse fun h => by cases h
    | .node _ _, .bind _ _ _ => isFalse fun h => by cases h
    | .trace _ _, .terminal _ _ => isFalse fun h => by cases h
    | .trace _ _, .node _ _ => isFalse fun h => by cases h
    | .trace _ _, .bind _ _ _ => isFalse fun h => by cases h
    | .bind _ _ _, .terminal _ _ => isFalse fun h => by cases h
    | .bind _ _ _, .node _ _ => isFalse fun h => by cases h
    | .bind _ _ _, .trace _ _ => isFalse fun h => by cases h

  /-- Helper: decidable equality for list of trees. -/
  def decEqList [DecidableEq C] [DecidableEq W] :
      (as bs : List (Tree C W)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse fun h => by cases h
    | _ :: _, [] => isFalse fun h => by cases h
    | a :: as, b :: bs =>
      match decEq a b, decEqList as bs with
      | isTrue ha, isTrue has => isTrue (by rw [ha, has])
      | isFalse ha, _ => isFalse fun h => by cases h; exact ha rfl
      | _, isFalse has => isFalse fun h => by cases h; exact has rfl
end

instance instDecidableEq [DecidableEq C] [DecidableEq W] : DecidableEq (Tree C W) := decEq

/-! ### Size -/

/-- Number of nodes in the tree. -/
def size : Tree C W → Nat
  | .terminal _ _ => 1
  | .node _ cs => 1 + sizeList cs
  | .trace _ _ => 1
  | .bind _ _ body => 1 + size body
where
  sizeList : List (Tree C W) → Nat
  | [] => 0
  | t :: ts => size t + sizeList ts

/-- Number of word-bearing terminals (leaves) in the tree.
    Traces and binders contribute 0; internal nodes recurse. -/
def leafCount : Tree C W → Nat
  | .terminal _ _ => 1
  | .node _ cs => leafCountList cs
  | .trace _ _ => 0
  | .bind _ _ body => leafCount body
where
  leafCountList : List (Tree C W) → Nat
  | [] => 0
  | t :: ts => leafCount t + leafCountList ts

/-! ### Induction principle -/

/-- Membership-based recursor/induction principle for `Tree`. The default
`induction` tactic refuses nested inductives, and the raw two-motive
`Tree.rec` forces a parallel `List` motive; this principle hands the
`node` case the hypothesis proofs actually want — `∀ t ∈ cs, motive t` —
so structural inductions read directly. With `@[elab_as_elim]`, used as
`induction t using Tree.recAux with | terminal … | node c cs ih | trace … | bind …`. -/
@[elab_as_elim]
def recAux {motive : Tree C W → Sort*}
    (terminal : ∀ c w, motive (.terminal c w))
    (node : ∀ c cs, (∀ t ∈ cs, motive t) → motive (.node c cs))
    (trace : ∀ n c, motive (.trace n c))
    (bind : ∀ n c b, motive b → motive (.bind n c b)) : ∀ t, motive t
  | .terminal c w => terminal c w
  | .node c cs    => node c cs (fun t _ => recAux terminal node trace bind t)
  | .trace n c    => trace n c
  | .bind n c b   => bind n c b (recAux terminal node trace bind b)
  termination_by t => sizeOf t
  decreasing_by
    · rename_i ht; have := List.sizeOf_lt_of_mem ht
      simp only [Tree.node.sizeOf_spec]; omega
    · simp only [Tree.bind.sizeOf_spec]; omega

/-! ### Subtrees -/

/-- All subtrees including self (pre-order traversal). -/
def subtrees : Tree C W → List (Tree C W)
  | t@(.terminal _ _) => [t]
  | t@(.node _ cs) => t :: subtreesList cs
  | t@(.trace _ _) => [t]
  | t@(.bind _ _ body) => t :: subtrees body
where
  subtreesList : List (Tree C W) → List (Tree C W)
  | [] => []
  | t :: ts => subtrees t ++ subtreesList ts

theorem subtreesList_eq_flatMap (cs : List (Tree C W)) :
    subtrees.subtreesList cs = cs.flatMap subtrees := by
  induction cs with
  | nil => rfl
  | cons t ts ih => simp [subtrees.subtreesList, ih, List.flatMap_cons]

theorem subtrees_node (cat : C) (cs : List (Tree C W)) :
    subtrees (.node cat cs) = .node cat cs :: cs.flatMap subtrees := by
  rw [subtrees, subtreesList_eq_flatMap]

/-! ### Category queries -/

/-- `ContainsCat target t` holds when category `target` appears on some
subtree of `t`. A `Prop` predicate (with a kernel-reducible `Decidable`
instance from `List` membership, so `decide` closes concrete goals) over
the file's own structurally-recursive `subtrees` — not a `Bool` function. -/
def ContainsCat [DecidableEq C] (target : C) (t : Tree C W) : Prop :=
  target ∈ (subtrees t).map cat

instance [DecidableEq C] (target : C) (t : Tree C W) :
    Decidable (ContainsCat target t) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `ContainsCat` at a node: it is the node's own category, or appears in
some child. -/
theorem containsCat_node_iff [DecidableEq C] (target cat : C)
    (cs : List (Tree C W)) :
    ContainsCat target (.node cat cs) ↔
      target = cat ∨ ∃ t ∈ cs, ContainsCat target t := by
  simp only [ContainsCat, subtrees_node, List.map_cons, List.mem_cons, List.mem_map,
    List.mem_flatMap, Tree.cat]
  constructor
  · rintro (h | ⟨s, ⟨t, ht, hts⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, s, hts, rfl⟩
  · rintro (rfl | ⟨t, ht, s, hs, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨s, ⟨t, ht, hs⟩, rfl⟩

/-- `ContainsCat` at a binder: the binder's category, or inside the body. -/
theorem containsCat_bind_iff [DecidableEq C] (target c : C) (n : Nat)
    (body : Tree C W) :
    ContainsCat target (.bind n c body) ↔ target = c ∨ ContainsCat target body := by
  simp only [ContainsCat, subtrees, List.map_cons, List.mem_cons, Tree.cat]

/-! ### Leaf substitution -/

/-- Substitute all terminals of category `c` carrying word `target`
with `replacement`. This is the most common structural operation:
replacing one scalar item with another of the same category. -/
def leafSubst [BEq C] [BEq W] (target replacement : W) (c : C) :
    Tree C W → Tree C W
  | .terminal c' w =>
    if c == c' && w == target then .terminal c' replacement
    else .terminal c' w
  | .node c' cs => .node c' (leafSubstList target replacement c cs)
  | .trace n c' => .trace n c'
  | .bind n c' body => .bind n c' (leafSubst target replacement c body)
where
  leafSubstList (target replacement : W) (c : C) :
      List (Tree C W) → List (Tree C W)
  | [] => []
  | t :: ts => leafSubst target replacement c t ::
               leafSubstList target replacement c ts

end Tree

/-! ### `Branching` instance: positions, dominance, command relations

The path machinery (Gorn addresses, `Core.Order.TreePath`, the
dominance order, the B&P command-relation bridge) is generic over
`Core.Order.Branching`; `Tree` participates through the instance
below. `Branching.subtreeAt` at this instance behaves as before: for
`node c cs` the next index selects `cs[i]?`; for `bind` only index `0`
is valid (binders have a single body); terminals and traces have no
children. Positions inherit mathlib's rooted-tree order stack from
`TreePath`: root `⊥`, parent `Order.pred`, least common ancestor `⊓`. -/

instance {C W : Type*} : Core.Order.Branching (Tree C W) where
  children
    | .terminal _ _ => []
    | .node _ cs => cs
    | .trace _ _ => []
    | .bind _ _ body => [body]

/-- Children strictly decrease the `sizeOf` measure, unlocking the
generic recursion API (`Branching.size`, `subtrees`, `yield`,
`inductionOn`). `noncomputable` because the `measure` field stores
`sizeOf`, whose nested-`List` IR the LCNF boxing pass cannot compile;
the measure is only a termination witness, and `yield`/`size` reduce
symbolically via their `_def` lemmas. -/
instance {C W : Type*} : Core.Order.IsFiniteBranching (Tree C W) :=
  .ofMeasure sizeOf fun {c t} hc => by
    cases t with
    | terminal _ _ => simp [Core.Order.Branching.children] at hc
    | node _ cs =>
      simp only [Core.Order.Branching.children] at hc
      have := List.sizeOf_lt_of_mem hc
      simp only [Tree.node.sizeOf_spec]
      omega
    | trace _ _ => simp [Core.Order.Branching.children] at hc
    | bind _ _ body =>
      simp only [Core.Order.Branching.children, List.mem_singleton] at hc
      subst hc
      simp only [Tree.bind.sizeOf_spec]
      omega

/-- Terminal content: the word at a `terminal`; traces, binders, and
internal nodes are contentless, so `Branching.yield` computes the
frontier string. -/
instance {C W : Type*} : Core.Order.HasContent (Tree C W) W where
  content?
    | .terminal _ w => some w
    | _ => none

/-! ### `Branching.yield`-instance simp lemmas

Make the generic `Branching.yield` reduce by `simp`/`decide` at
concrete `Tree` constructors — the prerequisite for consumers (Studies
files) to replace bespoke yield computations with the generic API. -/

@[simp] theorem branching_content_terminal {C W : Type*} (c : C) (w : W) :
    Core.Order.HasContent.content? (Tree.terminal c w) = some w := rfl

@[simp] theorem branching_content_node {C W : Type*} (c : C)
    (cs : List (Tree C W)) :
    Core.Order.HasContent.content? (Tree.node c cs) = (none : Option W) := rfl

@[simp] theorem branching_content_trace {C W : Type*} (n : Nat) (c : C) :
    Core.Order.HasContent.content? (Tree.trace (W := W) n c) = none := rfl

@[simp] theorem branching_content_bind {C W : Type*} (n : Nat) (c : C)
    (body : Tree C W) :
    Core.Order.HasContent.content? (Tree.bind n c body) = none := rfl

@[simp] theorem branching_yield_terminal {C W : Type*} (c : C) (w : W) :
    Core.Order.Branching.yield (Tree.terminal c w) = [w] := by
  rw [Core.Order.Branching.yield_def]; rfl

@[simp] theorem branching_yield_node {C W : Type*} (c : C) (cs : List (Tree C W)) :
    Core.Order.Branching.yield (W := W) (Tree.node c cs) = cs.flatMap Core.Order.Branching.yield := by
  rw [Core.Order.Branching.yield_def]; rfl

@[simp] theorem branching_yield_trace {C W : Type*} (n : Nat) (c : C) :
    Core.Order.Branching.yield (Tree.trace (W := W) n c) = [] := by
  rw [Core.Order.Branching.yield_def]; rfl

@[simp] theorem branching_yield_bind {C W : Type*} (n : Nat) (c : C)
    (body : Tree C W) :
    Core.Order.Branching.yield (W := W) (Tree.bind n c body)
      = Core.Order.Branching.yield body := by
  rw [Core.Order.Branching.yield_def]
  show ([] : List W) ++ ([body].flatMap Core.Order.Branching.yield) = _
  simp

end Syntax

/-! ### FreeMagma → Tree forgetful map -/

namespace FreeMagma

/-- Forgetful map from a free magma to a binary `Syntax.Tree Unit α`.

The image lives in a strict subset of `Tree Unit α`: only `.terminal ()`
(from `.of`) and the binary `.node () [_, _]` (from `.mul`) are produced;
the n-ary `.node`, `.trace`, and `.bind` constructors are never used.

By composition with `Core.Order.Branching.toTreeOrder`, every
`FreeMagma α` inherits a `Core.Order.TreeOrder Core.Order.TreePath`,
making B&P's framework-agnostic command-relation library
(`Linglib.Core.Order.Command`) directly applicable.

Universe-polymorphic in `α`, matching `Syntax.Tree`. -/
def toTree {α : Type*} : FreeMagma α → Syntax.Tree Unit α
  | .of a => .terminal () a
  | .mul l r => .node () [l.toTree, r.toTree]

end FreeMagma
