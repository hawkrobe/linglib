import Linglib.Core.Lexical.UD

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

end Core.Tree
