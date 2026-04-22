import Mathlib.Data.List.Infix
import Mathlib.Algebra.Free
import Linglib.Core.Lexical.UD
import Linglib.Core.Order.Tree

/-!
# Trees

Unified tree type parameterized by node labels (`C`) and terminal content (`W`).

## `Tree C W` — The Y-Model Tree

N-ary branching with categories on every node. Supports both:
- **Compositional interpretation** (LF): `interp`/`evalTree`
  in `Composition/Tree.lean` — type-driven, ignores categories
- **Structural operations** (PF): @cite{katzir-2007} `StructOp` (substitution,
  deletion, contraction) in `Alternatives/Structural.lean` — category-aware

Parameterized by category type `C` (UD tags, CCG categories, feature
bundles, `Unit` for unlabeled, ...) and terminal type `W`.

### Instantiations

- `Tree Unit String` — category-free, for H&K composition. Use convenience
  constructors `.leaf`, `.bin`, `.un`, `.tr`, `.binder`.
- `Tree Cat String` — UD-grounded categories, for Katzir structural alternatives.
- `Tree Unit LIToken` — bare phrase structure, for Minimalist syntax
  (categories inside `LIToken`, not on nodes).

## `Cat` — Default Category System

Grounded in Universal Dependencies UPOS. Word-level categories via
`head : UPOS → Cat`, phrasal via `proj : UPOS → Cat`, plus `S` and `CP`.

## `TreePath` and `Tree.toTreeOrder`

A `TreePath` is a list of child indices identifying a subtree position.
The forgetful map `Tree.toTreeOrder` extracts the dominance partial order
from any `Tree C W` as a `Core.Order.TreeOrder TreePath`, making the
B&P command-relation library (`Linglib.Core.Order.Command`) applicable
to concrete trees regardless of category type.
-/

namespace Core.Tree

-- ════════════════════════════════════════════════════════════════════
-- §1  Default Category System (UD-grounded)
-- ════════════════════════════════════════════════════════════════════

open UD

/-- Default syntactic category system grounded in Universal Dependencies
UPOS (@cite{de-marneffe-zeman-2021}).

- `head pos` — word-level (terminal): wraps a UPOS tag directly
- `proj pos` — maximal X-bar projection of a UPOS head
- `S` — sentence/clause (not a projection of a single lexical head)
- `CP` — complementizer phrase

Phrasal categories are derived systematically: NP = `proj .NOUN`,
VP = `proj .VERB`, DP = `proj .DET`, ConjP = `proj .CCONJ`, etc.

This is one possible instantiation of `Tree`'s `C` parameter.
Framework-specific category systems (CCG functors, Minimalist
feature bundles, etc.) can be used instead. -/
inductive Cat where
  | head : UPOS → Cat
  | proj : UPOS → Cat
  | S
  | CP
  deriving DecidableEq, Repr

instance : Inhabited Cat := ⟨.S⟩

instance : BEq Cat := ⟨λ a b => decide (a = b)⟩

instance : LawfulBEq Cat where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

-- ── Abbreviations ──────────────────────────────────────────────────
-- Short names matching traditional notation. Each abbreviation is
-- marked @[match_pattern] so it can be used in pattern position.

namespace Cat

-- Word-level (heads / terminals)
@[match_pattern] abbrev N     : Cat := .head .NOUN
@[match_pattern] abbrev V     : Cat := .head .VERB
@[match_pattern] abbrev Det   : Cat := .head .DET
@[match_pattern] abbrev Adj   : Cat := .head .ADJ
@[match_pattern] abbrev Adv   : Cat := .head .ADV
@[match_pattern] abbrev P     : Cat := .head .ADP
@[match_pattern] abbrev Conj  : Cat := .head .CCONJ
@[match_pattern] abbrev Neg   : Cat := .head .PART
@[match_pattern] abbrev C     : Cat := .head .SCONJ
@[match_pattern] abbrev Num   : Cat := .head .NUM
@[match_pattern] abbrev Pron  : Cat := .head .PRON
@[match_pattern] abbrev Aux   : Cat := .head .AUX

-- Phrasal (maximal projections)
@[match_pattern] abbrev NP    : Cat := .proj .NOUN
@[match_pattern] abbrev VP    : Cat := .proj .VERB
@[match_pattern] abbrev DP    : Cat := .proj .DET
@[match_pattern] abbrev PP    : Cat := .proj .ADP
@[match_pattern] abbrev AdjP  : Cat := .proj .ADJ
@[match_pattern] abbrev AdvP  : Cat := .proj .ADV
@[match_pattern] abbrev ConjP : Cat := .proj .CCONJ
@[match_pattern] abbrev NegP  : Cat := .proj .PART
@[match_pattern] abbrev NumP  : Cat := .proj .NUM

end Cat


-- ════════════════════════════════════════════════════════════════════
-- §2  Unified Tree Type
-- ════════════════════════════════════════════════════════════════════

/-- Framework-neutral tree, parameterized by node label type `C`
and terminal word type `W`.

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
inductive Tree (C : Type) (W : Type) where
  | terminal : C → W → Tree C W
  | node     : C → List (Tree C W) → Tree C W
  | trace    : Nat → C → Tree C W
  | bind     : Nat → C → Tree C W → Tree C W
  deriving Repr

namespace Tree

variable {C W : Type}

-- ── Convenience constructors for C = Unit ─────────────────────────
-- Category-free trees (for H&K composition, Minimalism, etc.) use
-- these to avoid writing `()` everywhere.

@[match_pattern] abbrev leaf (w : W) : Tree Unit W := .terminal () w
@[match_pattern] abbrev un (t : Tree Unit W) : Tree Unit W := .node () (t :: [])
@[match_pattern] abbrev bin (t1 t2 : Tree Unit W) : Tree Unit W := .node () (t1 :: t2 :: [])
@[match_pattern] abbrev tr (n : Nat) : Tree Unit W := .trace n ()
@[match_pattern] abbrev binder (n : Nat) (body : Tree Unit W) : Tree Unit W := .bind n () body

-- ════════════════════════════════════════════════════════════════════
-- §3  Basic Accessors
-- ════════════════════════════════════════════════════════════════════

/-- Category label of the root node. Total: every constructor carries
a category (including `bind`, where it labels the result of PA). -/
def cat : Tree C W → C
  | .terminal c _ => c
  | .node c _ => c
  | .trace _ c => c
  | .bind _ c _ => c

-- ════════════════════════════════════════════════════════════════════
-- §4  Structural Equality
-- ════════════════════════════════════════════════════════════════════

/-- Structural equality for trees (mutual recursion through List). -/
def beq [BEq C] [BEq W] : Tree C W → Tree C W → Bool
  | .terminal c₁ w₁, .terminal c₂ w₂ => c₁ == c₂ && w₁ == w₂
  | .node c₁ cs₁, .node c₂ cs₂ => c₁ == c₂ && beqList cs₁ cs₂
  | .trace n₁ c₁, .trace n₂ c₂ => n₁ == n₂ && c₁ == c₂
  | .bind n₁ c₁ b₁, .bind n₂ c₂ b₂ => n₁ == n₂ && c₁ == c₂ && beq b₁ b₂
  | _, _ => false
where
  beqList : List (Tree C W) → List (Tree C W) → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false

instance [BEq C] [BEq W] : BEq (Tree C W) := ⟨beq⟩

-- ── Decidable equality (manual: nested-inductive `deriving` fails) ──

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

instance [DecidableEq C] [DecidableEq W] : DecidableEq (Tree C W) := decEq

-- ════════════════════════════════════════════════════════════════════
-- §5  Size
-- ════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════
-- §5b  Binary-Tree Recursor (for `Tree Unit W`)
-- ════════════════════════════════════════════════════════════════════

/-- Custom recursor for binary trees over `Tree Unit W`. The default
`induction` tactic refuses nested inductives like `Tree`; this recursor
expands the `node`-case enumeration so each non-binary arity (0, 1, ≥3
children) gets its own branch, separate from the binary `binNode` case
that carries inductive hypotheses. With `@[elab_as_elim]`, used as
`induction t using Tree.binRec with | term … | binNode … | tr … | bd … | nilNode | singletonNode … | manyNode …`. -/
@[elab_as_elim]
def binRec {W : Type} {motive : Tree Unit W → Sort*}
    (term : ∀ w, motive (.terminal () w))
    (binNode : ∀ l r, motive l → motive r → motive (.node () [l, r]))
    (tr : ∀ n, motive (.trace n ()))
    (bd : ∀ n body, motive body → motive (.bind n () body))
    (nilNode : motive (.node () []))
    (singletonNode : ∀ c, motive (.node () [c]))
    (manyNode : ∀ c1 c2 c3 cs, motive (.node () (c1 :: c2 :: c3 :: cs)))
    : ∀ t, motive t
  | .terminal () w => term w
  | .node () [] => nilNode
  | .node () [c] => singletonNode c
  | .node () [l, r] => binNode l r
      (binRec term binNode tr bd nilNode singletonNode manyNode l)
      (binRec term binNode tr bd nilNode singletonNode manyNode r)
  | .node () (c1 :: c2 :: c3 :: cs) => manyNode c1 c2 c3 cs
  | .trace n () => tr n
  | .bind n () body => bd n body
      (binRec term binNode tr bd nilNode singletonNode manyNode body)
termination_by t => t.size
decreasing_by all_goals (simp only [Tree.size, Tree.size.sizeList]; omega)

-- ════════════════════════════════════════════════════════════════════
-- §6  Subtrees
-- ════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════
-- §7  Category Queries
-- ════════════════════════════════════════════════════════════════════

/-- Whether a category appears anywhere in the tree. -/
def containsCat [BEq C] (target : C) : Tree C W → Bool
  | .terminal c _ => target == c
  | .node c cs => target == c || containsCatList target cs
  | .trace _ c => target == c
  | .bind _ c body => target == c || containsCat target body
where
  containsCatList (target : C) : List (Tree C W) → Bool
  | [] => false
  | t :: ts => containsCat target t || containsCatList target ts

-- ════════════════════════════════════════════════════════════════════
-- §8  Leaf Substitution
-- ════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════
-- §9  TreePath and Forgetful Map to TreeOrder
-- ════════════════════════════════════════════════════════════════════

/-- A path from the root of a tree, encoded as a list of child indices.

Each element is the index in the parent's child list (or `0` for the
unique child of a `bind`). The empty path identifies the root. -/
structure TreePath where
  /-- The underlying list of child indices. -/
  toList : List Nat

namespace TreePath

/-- Dominance order: `p ≤ q` iff `p` is a prefix of `q`. -/
instance : LE TreePath := ⟨fun p q => p.toList <+: q.toList⟩

instance : PartialOrder TreePath where
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm a b h₁ h₂ := by
    cases a; cases b
    have := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le
    simpa using this

/-- Two prefixes of the same list are comparable. This is the **Connected
    Ancestor Condition (CAC)** for the prefix order. -/
theorem prefix_or_prefix {p q r : TreePath} (hp : p ≤ r) (hq : q ≤ r) :
    p ≤ q ∨ q ≤ p := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq
  have heq : p.toList ++ s = q.toList ++ t := hs.trans ht.symm
  rcases List.append_eq_append_iff.1 heq with ⟨a', hqeq, _⟩ | ⟨c', hpeq, _⟩
  · left; exact ⟨a', hqeq.symm⟩
  · right; exact ⟨c', hpeq.symm⟩

end TreePath

namespace Tree

variable {C W : Type}

/-- Subtree at the given path; `none` if the path leaves the tree.

For `node c cs`, the next index `i` selects child `cs[i]?`; for
`bind`, only index `0` is valid (binders have a single body). -/
def subtreeAt : Tree C W → List Nat → Option (Tree C W)
  | t,                  []          => some t
  | .node _ cs,         (i :: rest) =>
      (cs[i]?).bind (fun child => subtreeAt child rest)
  | .bind _ _ body,     (0 :: rest) => subtreeAt body rest
  | .bind _ _ _,        (_ :: _)    => none
  | .terminal _ _,      (_ :: _)    => none
  | .trace _ _,         (_ :: _)    => none

/-- Set of valid paths in the tree (paths that resolve to a subtree). -/
def validPaths (t : Tree C W) : Set TreePath :=
  {p | (t.subtreeAt p.toList).isSome}

theorem nil_validPath (t : Tree C W) : (⟨[]⟩ : TreePath) ∈ t.validPaths := by
  simp [validPaths, subtreeAt]

/-- **Forgetful map** from a `Tree C W` to its dominance order as a
    `TreeOrder TreePath`. This makes the framework-agnostic command-
    relation library (@cite{barker-pullum-1990}, B&P) directly applicable
    to any concrete tree, regardless of category or word type. -/
def toTreeOrder (t : Tree C W) : Core.Order.TreeOrder TreePath where
  nodes := t.validPaths
  root := ⟨[]⟩
  root_in_nodes := t.nil_validPath
  root_le_all := fun _ _ => List.nil_prefix
  ancestor_connected _ _ _ h₁ h₂ := TreePath.prefix_or_prefix h₁ h₂

end Tree

end Core.Tree

-- ════════════════════════════════════════════════════════════════════
-- §10  FreeMagma → Tree forgetful map
-- ════════════════════════════════════════════════════════════════════

namespace FreeMagma

/-- Forgetful map from a free magma to a binary `Core.Tree.Tree Unit α`.

The image lives in a strict subset of `Tree Unit α`: only `.terminal ()`
(from `.of`) and the binary `.node () [_, _]` (from `.mul`) are produced;
the n-ary `.node`, `.trace`, and `.bind` constructors are never used.

By composition with `Core.Tree.Tree.toTreeOrder`, every `FreeMagma α`
inherits a `Core.Order.TreeOrder Core.Tree.TreePath`, making B&P's
framework-agnostic command-relation library
(`Linglib.Core.Order.Command`) directly applicable.

Universe note: capped at `α : Type` because `Core.Tree.Tree` is monomorphic
in `Type 0`; sufficient for `LIToken`-indexed `SyntacticObject`. -/
def toTree {α : Type} : FreeMagma α → Core.Tree.Tree Unit α
  | .of a => .terminal () a
  | .mul l r => .node () [l.toTree, r.toTree]

end FreeMagma
