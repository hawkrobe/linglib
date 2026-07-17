import Linglib.Core.Order.Branching

/-!
# Nanosyntax: Tree-Based Spellout
[taraldsen-et-al-2018] [caha-2009] [starke-2009]

Extension of rank-based Superset spellout
(`Morphology/Nanosyntax/Superset.lean`) to tree-structured spellout. Implements the Superset Principle (SP) for trees: a lexical
entry M ↔ S' can spell out syntactic target S if S' structurally
contains S (`NanoTree.Contains`). Among matching entries, the Elsewhere
Condition selects the smallest (by tree size).

The SP on trees is a consequence of [starke-2009]'s Matching relation
(formalized in [taraldsen-et-al-2018] as (35)): M matches S iff there
exists a node N in M's stored tree such that S and N have the same root
label and mutually matching daughters. For the right-branching
single-daughter trees used in Bantu class prefix analysis, structural
containment and bidirectional Matching coincide; the implementation
uses containment as the simpler equivalent formulation.

## Main declarations

- `NanoTree`: feature trees; `NanoTree.Contains`: sub-constituency
- `TreeLexEntry`: a stored tree paired with an exponent; `TreeLexEntry.Matches`
- `treeSpellout`: Superset Principle + Elsewhere Condition
- `FootConditionMet`: [taraldsen-et-al-2018]'s constraint on backtracking
- `chain_contains_iff_le`: for right-branching chains, tree containment
  reduces to rank comparison — tree-based spellout generalizes (not
  replaces) rank-based spellout
-/

namespace Morphology.Nanosyntax

/-- Morphological type of an exponent derived from nanosyntactic
spellout. Suffixes arise from spellout-driven movement (roll-up, unary
foot); prefixes arise from subderivation (binary foot) — [dekier-2021]
for this diagnostic on indefinite markers. -/
inductive MorphType where
  | suffix | prefix
  deriving DecidableEq, Repr

/-! ### NanoTree -/

/-- A nanosyntactic feature tree. Simpler than `Syntax` — no
    traces, no binding, no category/word split. Just labeled nodes
    with an ordered list of daughters.

    `leaf f` = a terminal feature.
    `node f children` = feature f dominating daughters. -/
inductive NanoTree (F : Type*) where
  | leaf : F → NanoTree F
  | node : F → List (NanoTree F) → NanoTree F
  deriving Repr

namespace NanoTree

variable {F : Type*}

/-! ### Decidable equality

Defined by structural recursion (not `deriving DecidableEq`, which routes
the nested `List` through well-founded recursion and does not kernel-reduce;
`decide`-style spellout evaluations need the structural form). -/

/-- Structural decidable equality on trees. -/
protected def decEq [DecidableEq F] : (s t : NanoTree F) → Decidable (s = t)
  | .leaf f, .leaf g =>
    if h : f = g then .isTrue (h ▸ rfl)
    else .isFalse fun he => by cases he; exact h rfl
  | .leaf _, .node _ _ => .isFalse nofun
  | .node _ _, .leaf _ => .isFalse nofun
  | .node f cs, .node g ds =>
    if h : f = g then
      match NanoTree.decEq.decEqList cs ds with
      | .isTrue hl => .isTrue (h ▸ hl ▸ rfl)
      | .isFalse hl => .isFalse fun he => by cases he; exact hl rfl
    else .isFalse fun he => by cases he; exact h rfl
where
  /-- Structural decidable equality on daughter lists. -/
  decEqList [DecidableEq F] : (cs ds : List (NanoTree F)) → Decidable (cs = ds)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse nofun
    | _ :: _, [] => .isFalse nofun
    | c :: cs, d :: ds =>
      match NanoTree.decEq c d with
      | .isTrue h =>
        match NanoTree.decEq.decEqList cs ds with
        | .isTrue hl => .isTrue (h ▸ hl ▸ rfl)
        | .isFalse hl => .isFalse fun he => by cases he; exact hl rfl
      | .isFalse h => .isFalse fun he => by cases he; exact h rfl

instance [DecidableEq F] : DecidableEq (NanoTree F) := NanoTree.decEq

/-! ### Size -/

/-- Number of nodes in the tree. Used by the Elsewhere Condition
    to select the smallest matching entry. -/
def size : NanoTree F → Nat
  | .leaf _ => 1
  | .node _ children => 1 + sizeList children
where
  sizeList : List (NanoTree F) → Nat
    | [] => 0
    | t :: ts => t.size + sizeList ts

/-! ### Containment (Superset Principle on trees) -/

/-- `Contains self target`: `target` occurs in `self` as a sub-constituent.
    Implements the tree-generalized Superset Principle ([caha-2009] §2.2,
    [taraldsen-et-al-2018] (36)): entry M matches target S if M's stored
    tree contains S.

    For right-branching single-daughter trees (all Bantu class prefix
    structures), this is equivalent to the bidirectional Matching
    relation ([taraldsen-et-al-2018] (35)).

    For 1D chains: a chain of depth n contains all chains of depth
    k ≤ n, matching `ExponenceRule.Matches` (`chain_contains_iff_le`). -/
inductive Contains : NanoTree F → NanoTree F → Prop
  | refl (t : NanoTree F) : Contains t t
  | child {f : F} {cs : List (NanoTree F)} {c target : NanoTree F} :
      c ∈ cs → Contains c target → Contains (.node f cs) target

@[simp] theorem contains_leaf_iff {f : F} {t : NanoTree F} :
    Contains (.leaf f) t ↔ (.leaf f : NanoTree F) = t :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .refl _⟩

theorem contains_node_iff {f : F} {cs : List (NanoTree F)} {t : NanoTree F} :
    Contains (.node f cs) t ↔
      (.node f cs : NanoTree F) = t ∨ ∃ c ∈ cs, Contains c t := by
  constructor
  · rintro (_ | ⟨hmem, hc⟩)
    · exact .inl rfl
    · exact .inr ⟨_, hmem, hc⟩
  · rintro (h | ⟨c, hmem, hc⟩)
    · exact h ▸ .refl _
    · exact .child hmem hc

/-- Structural decision procedure for containment (kernel-reducible). -/
protected def decContains [DecidableEq F] :
    (s t : NanoTree F) → Decidable (Contains s t)
  | .leaf f, t =>
    if h : (.leaf f : NanoTree F) = t then .isTrue (h ▸ .refl _)
    else .isFalse fun hc => h (by cases hc; rfl)
  | .node f cs, t =>
    if h : (.node f cs : NanoTree F) = t then .isTrue (h ▸ .refl _)
    else
      match NanoTree.decContains.decAny cs t with
      | .isTrue hex => .isTrue (have ⟨_, hmem, hc⟩ := hex; .child hmem hc)
      | .isFalse hno => .isFalse fun hc => by
          cases hc with
          | refl => exact h rfl
          | child hmem hc => exact hno ⟨_, hmem, hc⟩
where
  /-- Does some member of `cs` contain `t`? -/
  decAny [DecidableEq F] :
      (cs : List (NanoTree F)) → (t : NanoTree F) →
        Decidable (∃ c ∈ cs, Contains c t)
    | [], _ => .isFalse fun ⟨_, hmem, _⟩ => by cases hmem
    | c :: cs, t =>
      match NanoTree.decContains c t with
      | .isTrue hc => .isTrue ⟨c, List.mem_cons_self .., hc⟩
      | .isFalse hc =>
        match NanoTree.decContains.decAny cs t with
        | .isTrue hex =>
          .isTrue (have ⟨d, hmem, hd⟩ := hex;
            ⟨d, List.mem_cons_of_mem _ hmem, hd⟩)
        | .isFalse hno => .isFalse fun ⟨d, hmem, hd⟩ => by
            cases hmem with
            | head => exact hc hd
            | tail _ hmem => exact hno ⟨d, hmem, hd⟩

instance [DecidableEq F] (s t : NanoTree F) : Decidable (Contains s t) :=
  NanoTree.decContains s t

/-! ### Foot -/

/-- The foot of a tree: the feature at the bottom of the leftmost
    spine. For right-branching chains [Fn [... [F0]]], the foot
    is F0 — the deepest feature on the functional sequence. -/
def foot : NanoTree F → F
  | .leaf f => f
  | .node f [] => f
  | .node _ (child :: _) => child.foot

end NanoTree

/-! ### Tree lexical entry -/

/-- A nanosyntactic lexical entry storing a tree rather than a scalar
    rank, paired with an exponent of type `α` (`String` in concrete
    fragments). The tree encodes the full feature geometry that the
    morpheme lexicalizes.

    Contrast with `ExponenceRule` (`Morphology/Exponence/Hierarchy.lean`)
    which stores only a span (depth on a 1D functional sequence). -/
structure TreeLexEntry (F : Type*) (α : Type*) where
  /-- The stored feature tree. -/
  tree : NanoTree F
  /-- The exponent. -/
  exponent : α
  /-- Morphological type (suffix or prefix). -/
  morphType : MorphType := .suffix
  deriving Repr

variable {F : Type*} {α : Type*}

/-- A tree-based entry matches a target under the Superset Principle
    iff its stored tree contains the target as a sub-constituent. -/
def TreeLexEntry.Matches (entry : TreeLexEntry F α) (target : NanoTree F) :
    Prop :=
  entry.tree.Contains target

instance [DecidableEq F] (entry : TreeLexEntry F α) (target : NanoTree F) :
    Decidable (entry.Matches target) :=
  inferInstanceAs (Decidable (NanoTree.Contains _ _))

/-! ### Tree spellout (Elsewhere Condition) -/

/-- Phrasal spellout via the tree-generalized Superset Principle:
    among entries whose tree contains the target, select the one
    with the smallest tree (most specific match).

    Parallels `Morphology.Containment.spellout`, but the matching
    relation is tree containment instead of rank comparison, and the
    specificity metric is tree size instead of rank. -/
def treeSpellout [DecidableEq F] (entries : List (TreeLexEntry F α))
    (target : NanoTree F) : Option α :=
  let matching := entries.filter fun e => decide (e.Matches target)
  (matching.foldl (init := none) fun acc entry =>
    match acc with
    | none => some entry
    | some prev =>
      if entry.tree.size < prev.tree.size then some entry
      else some prev
  ).map (·.exponent)

/-! ### Foot Condition -/

/-- The Foot Condition ([taraldsen-et-al-2018]): the foot of a lexical
    entry's stored tree must be present as a feature in the syntactic
    structure being spelled out.

    If entry M stores [X [...[Z]]], the Foot Condition requires that Z
    appear in the structure. This constrains backtracking: when spellout
    fails and the derivation splits the target into specifier +
    complement, only entries whose foot matches a feature in the
    remaining structure are eligible. -/
def FootConditionMet (entry : TreeLexEntry F α) (syntacticTree : NanoTree F) :
    Prop :=
  syntacticTree.Contains (.leaf entry.tree.foot)

instance [DecidableEq F] (entry : TreeLexEntry F α) (tree : NanoTree F) :
    Decidable (FootConditionMet entry tree) :=
  inferInstanceAs (Decidable (NanoTree.Contains _ _))

/-! ### Chain trees (bridge to 1D) -/

/-- Build a right-branching chain tree of depth n.
    `chainTree feat 0 = leaf (feat 0)`
    `chainTree feat 1 = node (feat 1) [leaf (feat 0)]`
    `chainTree feat n = node (feat n) [chainTree feat (n-1)]`

    A chain of depth n is isomorphic to an `ExponenceRule` spanning
    grade n in the 1D nanosyntax. -/
def chainTree (feat : Nat → F) : Nat → NanoTree F
  | 0 => .leaf (feat 0)
  | n + 1 => .node (feat (n + 1)) [chainTree feat n]

/-! ### Bridge theorems -/

theorem chainTree_succ (feat : Nat → F) (n : Nat) :
    chainTree feat (n + 1) = .node (feat (n + 1)) [chainTree feat n] := rfl

/-- Chain tree size is n + 1 (one node per feature level). -/
theorem chainTree_size (feat : Nat → F) (n : Nat) :
    (chainTree feat n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [chainTree, NanoTree.size, NanoTree.size.sizeList, ih]
    omega

/-- The foot of a chain tree is always feat 0 — the bottom of
    the functional sequence. -/
theorem chainTree_foot (feat : Nat → F) (n : Nat) :
    (chainTree feat n).foot = feat 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chainTree, NanoTree.foot, ih]

/-- Chains of distinct depths are distinct trees, regardless of the
    feature assignment — depth alone separates them. -/
theorem chainTree_injective (feat : Nat → F) :
    Function.Injective (chainTree feat) := fun n m h => by
  have hs := congrArg NanoTree.size h
  rwa [chainTree_size, chainTree_size, Nat.add_right_cancel_iff] at hs

/-- For right-branching chains, tree containment reduces to rank
    comparison: a chain of depth re contains a chain of depth r iff
    r ≤ re. This is exactly the matching condition of the rank-based
    `ExponenceRule.Matches`, establishing that tree-based spellout
    generalizes (not replaces) rank-based spellout.

    Unlike the previous Bool formulation, no injectivity of `feat` is
    needed: chain depth alone drives both directions. -/
theorem chain_contains_iff_le (feat : Nat → F) (re r : Nat) :
    (chainTree feat re).Contains (chainTree feat r) ↔ r ≤ re := by
  induction re generalizing r with
  | zero =>
    rw [chainTree, NanoTree.contains_leaf_iff]
    cases r with
    | zero => simp [chainTree]
    | succ r => simp [chainTree]
  | succ n ih =>
    rw [chainTree_succ, NanoTree.contains_node_iff, ← chainTree_succ,
      (chainTree_injective feat).eq_iff]
    simp only [List.mem_singleton, exists_eq_left, ih]
    omega

end Morphology.Nanosyntax

/-! ### Rose-tree interface instances

`NanoTree` joins the `Core.Order.Branching` tower. The structural
`size`/`decEq`/`decContains` above remain the kernel-computable
specializations ([file-level generality discipline]: WF-derived
generics do not kernel-reduce, so `decide`-style spell-out evaluations
need the structural forms). -/

namespace Morphology.Nanosyntax.NanoTree

instance {F : Type*} : Core.Order.Branching (NanoTree F) where
  children
    | .leaf _ => []
    | .node _ cs => cs

@[simp] theorem branching_children_leaf {F : Type*} (f : F) :
    Core.Order.Branching.children (NanoTree.leaf f) = [] := rfl

@[simp] theorem branching_children_node {F : Type*} (f : F)
    (cs : List (NanoTree F)) :
    Core.Order.Branching.children (NanoTree.node f cs) = cs := rfl

instance {F : Type*} : Core.Order.IsFiniteBranching (NanoTree F) :=
  .ofMeasure sizeOf fun {c t} hc => by
    cases t with
    | leaf _ => simp at hc
    | node f cs =>
      simp only [branching_children_node] at hc
      have := List.sizeOf_lt_of_mem hc
      simp only [NanoTree.node.sizeOf_spec]
      omega

end Morphology.Nanosyntax.NanoTree
