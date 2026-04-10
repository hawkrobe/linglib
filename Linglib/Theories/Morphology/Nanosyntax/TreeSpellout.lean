import Linglib.Theories.Morphology.Nanosyntax.Core

/-!
# Nanosyntax: Tree-Based Spellout
@cite{taraldsen-et-al-2018} @cite{caha-2009} @cite{starke-2009}

Extension of rank-based nanosyntax (`Core.lean`) to tree-structured
spellout. Implements the Superset Principle (SP) for trees:
a lexical entry M ↔ S' can spell out syntactic target S if S'
structurally contains S. Among matching entries, the Elsewhere
Condition selects the smallest (by tree size).

The SP on trees is a consequence of @cite{starke-2009}'s Matching
relation (formalized in @cite{taraldsen-et-al-2018} as (35)):
M matches S iff there exists a node N in M's stored tree such that
S and N have the same root label and mutually matching daughters.
For the right-branching single-daughter trees used in Bantu class
prefix analysis, structural containment (`NanoTree.contains`) and
bidirectional Matching coincide. The implementation uses containment
as the simpler equivalent formulation.

This generalization is needed for @cite{taraldsen-et-al-2018}'s
analysis of Bantu class prefixes, where lexical entries store
phrasal trees [# Nx] rather than scalar ranks on a case fseq.

## Bridge to rank-based spellout

For right-branching chains (single-daughter trees), tree-based
spellout reduces to rank-based spellout. A chain of depth n is
isomorphic to a rank-n `LexEntry` from `Core.lean`.
-/

namespace Theories.Morphology.Nanosyntax

-- ============================================================================
-- §1: NanoTree
-- ============================================================================

/-- A nanosyntactic feature tree. Simpler than `Core.Tree` — no
    traces, no binding, no category/word split. Just labeled nodes
    with an ordered list of daughters.

    `leaf f` = a terminal feature.
    `node f children` = feature f dominating daughters. -/
inductive NanoTree (F : Type) where
  | leaf : F → NanoTree F
  | node : F → List (NanoTree F) → NanoTree F
  deriving Repr

namespace NanoTree

variable {F : Type}

-- ============================================================================
-- §2: BEq (transparent, for proof reasoning)
-- ============================================================================

/-- Structural equality for nanosyntactic trees. Defined manually
    (not via `deriving BEq`) so that equations are transparent and
    available for `rfl`/`simp` proofs. -/
def beq [BEq F] : NanoTree F → NanoTree F → Bool
  | .leaf f, .leaf g => f == g
  | .node f cs, .node g ds => f == g && beq.beqList cs ds
  | _, _ => false
where
  beqList : List (NanoTree F) → List (NanoTree F) → Bool
    | [], [] => true
    | a :: as, b :: bs => NanoTree.beq a b && beqList as bs
    | _, _ => false

instance [BEq F] : BEq (NanoTree F) := ⟨NanoTree.beq⟩

@[simp] theorem beq_leaf_leaf [BEq F] (f g : F) :
    ((.leaf f : NanoTree F) == .leaf g) = (f == g) := rfl
@[simp] theorem beq_leaf_node [BEq F] (f g : F) (cs : List (NanoTree F)) :
    ((.leaf f : NanoTree F) == .node g cs) = false := rfl
@[simp] theorem beq_node_leaf [BEq F] (f : F) (cs : List (NanoTree F)) (g : F) :
    ((.node f cs : NanoTree F) == .leaf g) = false := rfl
@[simp] theorem beq_node_node [BEq F] (f g : F) (cs ds : List (NanoTree F)) :
    ((.node f cs : NanoTree F) == .node g ds) =
    (f == g && NanoTree.beq.beqList cs ds) := rfl
@[simp] theorem beqList_nil [BEq F] :
    (NanoTree.beq.beqList ([] : List (NanoTree F)) []) = true := rfl
@[simp] theorem beqList_cons [BEq F] (a b : NanoTree F)
    (as bs : List (NanoTree F)) :
    NanoTree.beq.beqList (a :: as) (b :: bs) =
    (a == b && NanoTree.beq.beqList as bs) := rfl

-- ============================================================================
-- §3: Size
-- ============================================================================

/-- Number of nodes in the tree. Used by the Elsewhere Condition
    to select the smallest matching entry. -/
def size : NanoTree F → Nat
  | .leaf _ => 1
  | .node _ children => 1 + sizeList children
where
  sizeList : List (NanoTree F) → Nat
    | [] => 0
    | t :: ts => t.size + sizeList ts

-- ============================================================================
-- §4: Containment (Superset Principle on trees)
-- ============================================================================

/-- Does `self` contain `target` as a sub-constituent?
    Implements the tree-generalized Superset Principle
    (@cite{caha-2009} §2.2, @cite{taraldsen-et-al-2018} (36)):
    entry M matches target S if M's stored tree contains S.

    For right-branching single-daughter trees (all Bantu class
    prefix structures), this is equivalent to the bidirectional
    Matching relation (@cite{taraldsen-et-al-2018} (35)).

    For 1D chains: a chain of depth n contains all chains of
    depth k <= n, matching `LexEntry.matches`. -/
def contains [BEq F] : NanoTree F → NanoTree F → Bool
  | .leaf f, target => .leaf f == target
  | .node f children, target =>
      .node f children == target || containsList children target
where
  containsList [BEq F] : List (NanoTree F) → NanoTree F → Bool
    | [], _ => false
    | c :: cs, target => c.contains target || containsList cs target

-- ============================================================================
-- §5: Foot
-- ============================================================================

/-- The foot of a tree: the feature at the bottom of the leftmost
    spine. For right-branching chains [Fn [... [F0]]], the foot
    is F0 — the deepest feature on the functional sequence. -/
def foot : NanoTree F → F
  | .leaf f => f
  | .node f [] => f
  | .node _ (child :: _) => child.foot

end NanoTree

-- ============================================================================
-- §6: Tree Lexical Entry
-- ============================================================================

/-- A nanosyntactic lexical entry storing a tree rather than a
    scalar rank. The tree encodes the full feature geometry that
    the morpheme lexicalizes.

    Contrast with `LexEntry` (Core.lean) which stores only a
    rank (depth on a 1D functional sequence). -/
structure TreeLexEntry (F : Type) where
  /-- The stored feature tree. -/
  tree : NanoTree F
  /-- The phonological exponent. -/
  exponent : String
  /-- Morphological type (suffix or prefix). -/
  morphType : MorphType := .suffix
  deriving Repr

/-- Does a tree-based entry match a target under the Superset
    Principle? The entry matches if its tree contains the target
    as a sub-constituent. -/
def TreeLexEntry.matches {F : Type} [BEq F]
    (entry : TreeLexEntry F) (target : NanoTree F) : Bool :=
  entry.tree.contains target

-- ============================================================================
-- §7: Tree Spellout (Elsewhere Condition)
-- ============================================================================

/-- Phrasal spellout via the tree-generalized Superset Principle:
    among entries whose tree contains the target, select the one
    with the smallest tree (most specific match).

    Parallels `spellout` from `Core.lean`, but the matching
    relation is tree containment instead of rank comparison, and
    the specificity metric is tree size instead of rank. -/
def treeSpellout {F : Type} [BEq F]
    (entries : List (TreeLexEntry F)) (target : NanoTree F) :
    Option String :=
  let matching := entries.filter (·.matches target)
  (matching.foldl (init := none) fun acc entry =>
    match acc with
    | none => some entry
    | some prev =>
      if entry.tree.size < prev.tree.size then some entry
      else some prev
  ).map (·.exponent)

-- ============================================================================
-- §8: Foot Condition
-- ============================================================================

/-- The Foot Condition (@cite{taraldsen-et-al-2018}): the foot
    of a lexical entry's stored tree must be present as a feature
    in the syntactic structure being spelled out.

    If entry M stores [X [...[Z]]], the Foot Condition requires
    that Z appear in the structure. This constrains backtracking:
    when spellout fails and the derivation splits the target into
    specifier + complement, only entries whose foot matches a
    feature in the remaining structure are eligible. -/
def footConditionMet {F : Type} [BEq F]
    (entry : TreeLexEntry F) (syntacticTree : NanoTree F) : Bool :=
  syntacticTree.contains (.leaf (entry.tree.foot))

-- ============================================================================
-- §9: Chain trees (bridge to 1D)
-- ============================================================================

/-- Build a right-branching chain tree of depth n.
    `chainTree feat 0 = leaf (feat 0)`
    `chainTree feat 1 = node (feat 1) [leaf (feat 0)]`
    `chainTree feat n = node (feat n) [chainTree feat (n-1)]`

    A chain of depth n is isomorphic to a rank-n `LexEntry` in
    the 1D nanosyntax. -/
def chainTree {F : Type} (feat : Nat → F) : Nat → NanoTree F
  | 0 => .leaf (feat 0)
  | n + 1 => .node (feat (n + 1)) [chainTree feat n]

-- ============================================================================
-- §10: Bridge theorems
-- ============================================================================

/-- Chain tree size is n + 1 (one node per feature level). -/
theorem chainTree_size {F : Type} (feat : Nat → F) (n : Nat) :
    (chainTree feat n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [chainTree, NanoTree.size, NanoTree.size.sizeList, ih]
    omega

/-- The foot of a chain tree is always feat 0 — the bottom of
    the functional sequence. -/
theorem chainTree_foot {F : Type} (feat : Nat → F) (n : Nat) :
    (chainTree feat n).foot = feat 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chainTree, NanoTree.foot, ih]

/-- `decide p || decide q = decide r` when `p ∨ q ↔ r`. -/
private theorem decide_or_iff {p q r : Prop} [Decidable p] [Decidable q]
    [Decidable r] (h : p ∨ q ↔ r) : (decide p || decide q) = decide r := by
  cases hp : decide p <;> cases hq : decide q <;> simp_all

/-- BEq of chain trees with injective features equals `decide`
    on the depth index. -/
private theorem chainTree_beq_eq_decide {F : Type} [DecidableEq F]
    (feat : Nat → F) (hInj : Function.Injective feat) (n m : Nat) :
    (chainTree feat n == chainTree feat m) = decide (n = m) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [chainTree]
    | succ m => simp [chainTree]
  | succ n ih =>
    cases m with
    | zero => simp [chainTree]
    | succ m =>
      simp only [chainTree, NanoTree.beq_node_node, NanoTree.beqList_cons,
        NanoTree.beqList_nil, Bool.and_true]
      rw [ih m]
      by_cases h : n = m
      · subst h; simp
      · have hfne : feat (n + 1) ≠ feat (m + 1) :=
          fun hfe => (by omega : n + 1 ≠ m + 1) (hInj hfe)
        have h1 : (feat (n + 1) == feat (m + 1)) = false :=
          show decide _ = false from decide_eq_false hfne
        simp [h1, decide_eq_false h]

/-- For right-branching chains with injective features, tree
    containment reduces to rank comparison: a chain of depth re
    contains a chain of depth r iff re >= r.

    This is exactly the matching condition of the rank-based
    `LexEntry.matches`, establishing that tree-based spellout
    generalizes (not replaces) rank-based spellout. -/
theorem chain_contains_iff_ge {F : Type} [DecidableEq F] (feat : Nat → F)
    (hInj : Function.Injective feat) (re r : Nat) :
    (chainTree feat re).contains (chainTree feat r) = decide (re ≥ r) := by
  induction re generalizing r with
  | zero =>
    cases r with
    | zero => simp [chainTree, NanoTree.contains]
    | succ r => simp [chainTree, NanoTree.contains]
  | succ n ih =>
    simp only [chainTree, NanoTree.contains, NanoTree.contains.containsList, Bool.or_false]
    rw [ih r]
    rw [show (NanoTree.node (feat (n + 1)) [chainTree feat n] == chainTree feat r)
        = (chainTree feat (n + 1) == chainTree feat r) from rfl]
    rw [chainTree_beq_eq_decide feat hInj]
    exact decide_or_iff (by omega)

end Theories.Morphology.Nanosyntax
