import Linglib.Core.Lexical.UD

/-!
# Syntactic Trees

Framework-neutral tree type for representing syntactic structure.
Used by both compositional interpretation (@cite{heim-kratzer-1998})
and structural alternative generation (@cite{katzir-2007}).

## Design

`SynTree C W` is parameterized by:
- `C` — category type (UD UPOS tags, CCG categories, feature bundles, ...)
- `W` — word/terminal type (`String` for interpretation, finite enum for examples)

Four constructors:
- `terminal` — lexical item with category and word
- `node` — internal node with category and children (n-ary)
- `trace` — movement trace with binding index and category
- `bind` — λ-abstraction site with index, category, and body

The tree type is maximally permissive: it allows n-ary branching, traces,
and binding simultaneously. Framework-specific well-formedness constraints
(binary branching for Minimalism, no traces for CCG, etc.) are expressed
as predicates on trees, not as type-level restrictions.

Each syntax theory defines its own `C`:
- Minimalism: feature bundles
- CCG: complex functor categories (`S\NP`, etc.)
- HPSG: feature structures
- UD: `UPOS` flat tags

`Cat` (defined below) provides a convenient default for theory-neutral
work, grounding word-level categories in UD UPOS and deriving phrasal
categories via X-bar projection. It is not privileged — any `C` with
`BEq` works.
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

This is one possible instantiation of `SynTree`'s `C` parameter.
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
-- §2  Syntactic Trees
-- ════════════════════════════════════════════════════════════════════

/-- Framework-neutral syntactic tree, parameterized by category type `C`
and terminal word type `W`.

- `terminal c w` — leaf carrying category `c` and word `w`
- `node c cs` — internal node with category `c` and children `cs`
- `trace n c` — movement trace with index `n` and category `c`
- `bind n c body` — λ-abstraction with index `n`, category `c`, scope `body`

The `node` constructor takes a `List` of children, subsuming both
binary branching (for Heim & Kratzer composition) and n-ary structure
(for Katzir's deletion operation). Binary nodes are `node c [l, r]`.

`trace` and `bind` support Quantifier Raising and variable binding.
Frameworks without movement (CCG, HPSG) simply never construct these. -/
inductive SynTree (C : Type) (W : Type) where
  | terminal : C → W → SynTree C W
  | node     : C → List (SynTree C W) → SynTree C W
  | trace    : Nat → C → SynTree C W
  | bind     : Nat → C → SynTree C W → SynTree C W
  deriving Repr

namespace SynTree

variable {C W : Type}

-- ════════════════════════════════════════════════════════════════════
-- §3  Basic Accessors
-- ════════════════════════════════════════════════════════════════════

/-- Category label of the root node. Total: every constructor carries
a category (including `bind`, where it labels the result of PA). -/
def cat : SynTree C W → C
  | .terminal c _ => c
  | .node c _ => c
  | .trace _ c => c
  | .bind _ c _ => c

-- ════════════════════════════════════════════════════════════════════
-- §4  Structural Equality
-- ════════════════════════════════════════════════════════════════════

/-- Structural equality for trees (mutual recursion through List). -/
def beq [BEq C] [BEq W] : SynTree C W → SynTree C W → Bool
  | .terminal c₁ w₁, .terminal c₂ w₂ => c₁ == c₂ && w₁ == w₂
  | .node c₁ cs₁, .node c₂ cs₂ => c₁ == c₂ && beqList cs₁ cs₂
  | .trace n₁ c₁, .trace n₂ c₂ => n₁ == n₂ && c₁ == c₂
  | .bind n₁ c₁ b₁, .bind n₂ c₂ b₂ => n₁ == n₂ && c₁ == c₂ && beq b₁ b₂
  | _, _ => false
where
  beqList : List (SynTree C W) → List (SynTree C W) → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false

instance [BEq C] [BEq W] : BEq (SynTree C W) := ⟨beq⟩

-- ════════════════════════════════════════════════════════════════════
-- §5  Size
-- ════════════════════════════════════════════════════════════════════

/-- Number of nodes in the tree. -/
def size : SynTree C W → Nat
  | .terminal _ _ => 1
  | .node _ cs => 1 + sizeList cs
  | .trace _ _ => 1
  | .bind _ _ body => 1 + size body
where
  sizeList : List (SynTree C W) → Nat
  | [] => 0
  | t :: ts => size t + sizeList ts

-- ════════════════════════════════════════════════════════════════════
-- §6  Subtrees
-- ════════════════════════════════════════════════════════════════════

/-- All subtrees including self (pre-order traversal). -/
def subtrees : SynTree C W → List (SynTree C W)
  | t@(.terminal _ _) => [t]
  | t@(.node _ cs) => t :: subtreesList cs
  | t@(.trace _ _) => [t]
  | t@(.bind _ _ body) => t :: subtrees body
where
  subtreesList : List (SynTree C W) → List (SynTree C W)
  | [] => []
  | t :: ts => subtrees t ++ subtreesList ts

-- ════════════════════════════════════════════════════════════════════
-- §7  Category Queries
-- ════════════════════════════════════════════════════════════════════

/-- Whether a category appears anywhere in the tree. -/
def containsCat [BEq C] (target : C) : SynTree C W → Bool
  | .terminal c _ => target == c
  | .node c cs => target == c || containsCatList target cs
  | .trace _ c => target == c
  | .bind _ c body => target == c || containsCat target body
where
  containsCatList (target : C) : List (SynTree C W) → Bool
  | [] => false
  | t :: ts => containsCat target t || containsCatList target ts

-- ════════════════════════════════════════════════════════════════════
-- §8  Leaf Substitution
-- ════════════════════════════════════════════════════════════════════

/-- Substitute all terminals of category `c` carrying word `target`
with `replacement`. This is the most common structural operation:
replacing one scalar item with another of the same category. -/
def leafSubst [BEq C] [BEq W] (target replacement : W) (c : C) :
    SynTree C W → SynTree C W
  | .terminal c' w =>
    if c == c' && w == target then .terminal c' replacement
    else .terminal c' w
  | .node c' cs => .node c' (leafSubstList target replacement c cs)
  | .trace n c' => .trace n c'
  | .bind n c' body => .bind n c' (leafSubst target replacement c body)
where
  leafSubstList (target replacement : W) (c : C) :
      List (SynTree C W) → List (SynTree C W)
  | [] => []
  | t :: ts => leafSubst target replacement c t ::
               leafSubstList target replacement c ts

end SynTree

end Core.Tree
