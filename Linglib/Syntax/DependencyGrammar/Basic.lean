import Mathlib.Data.List.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Linglib.Data.UD.Basic
import Linglib.Morphology.Word.Basic

/-!
# Dependency grammar substrate

Core data types for dependency grammar: words connected by typed directed
edges (`Dependency`), graphs built over them (`Graph`), and single-headed
trees (`Tree`). Dependency relations use `UD.DepRel` from
`Data/UD/Basic.lean` (Universal Dependencies v2). [hudson-2010],
[gibson-2025].

## Main declarations

* `Dependency`, `Graph`, `Tree` — the basic graph-shaped data;
  `Tree extends Graph` with argument-structure frames.
* `Graph.parentsOf`, `children`, `inDegree`, `toDigraph` — the graph API;
  `toDigraph` presents the graph as a mathlib `Digraph` with decidable
  adjacency (`ParentEdge` is the adjacency at the edge-list level), and
  `toDigraph_mono` orders basic below enhanced graphs in the `Digraph` lattice.
* `hasUniqueHeads`, `isAcyclic`, `Tree.WF` — structural well-formedness.
* `numberAgreesOn` — number agreement across the edges of one relation.

The valency layer — frame schemas and their satisfaction — lives in
`Valency.lean`; only the slot data types (`Dir`, `ArgSlot`, `ArgStr`) are
declared here, because `Tree.frames` carries them.

## Implementation notes

* Predicate-shape definitions return `Bool` rather than `Prop` +
  `[Decidable]`; this is a substrate-wide convention that downstream files
  inherit, and migrating it is a separate refactor.
-/

open Morphology (Word)

namespace DependencyGrammar


section ArgumentStructure

/-- Direction of a dependent relative to its head. -/
inductive Dir where
  /-- The dependent precedes the head. -/
  | left
  /-- The dependent follows the head. -/
  | right
  deriving Repr, DecidableEq

/-- Whether a dependent at position `dep` sits on side `dir` of the head at
    position `head`. -/
def Dir.admits : Dir → Nat → Nat → Bool
  | .left, head, dep => dep < head
  | .right, head, dep => head < dep

/-- A single argument slot in an argument structure: which relation fills it,
    on which side of the head, and whether it must be filled. -/
structure ArgSlot where
  /-- The UD relation of the filler. -/
  depType : UD.DepRel
  /-- Which side of the head the filler sits. -/
  dir : Dir
  /-- Whether the slot must be filled. -/
  required : Bool := true
  deriving Repr, DecidableEq

/-- Argument structure: the dependent slots a word requires or allows. -/
abbrev ArgStr := List ArgSlot

end ArgumentStructure

/-! ### Dependencies and trees -/

section DependenciesAndTrees

/-- A dependency: directed edge from head to dependent. -/
structure Dependency where
  /-- Index of the head word in the sentence's `words` list. -/
  headIdx : Nat
  /-- Index of the dependent word in the sentence's `words` list. -/
  depIdx : Nat
  /-- The UD v2 relation label; length metrics ignore it. -/
  depType : UD.DepRel
  deriving Repr, DecidableEq

/-- A dependency graph for a sentence: tokens in surface order plus directed
    head → dependent edges. A word may carry several incoming arcs, as in the
    UD *enhanced* representation; the single-headed case is `Tree`. -/
structure Graph where
  /-- The sentence's tokens, in surface order. -/
  words : List Word
  /-- Directed head → dependent edges. -/
  deps : List Dependency
  /-- Index into `words` of the sentence root. -/
  rootIdx : Nat
  deriving Repr

/-- The mathlib `Digraph` on word positions whose edges are the arcs of
    `deps`, head → dependent. Constructed with `Digraph.mk'`, so adjacency is
    decidable and digraph-level goals close by `decide`. This is *the*
    adjacency of the theory: `ParentEdge` is its `Adj`, and `Dominates` its
    reachability. -/
def edgeDigraph (deps : List Dependency) : Digraph Nat :=
  Digraph.mk' λ v w => deps.any λ d => d.headIdx == v && d.depIdx == w

/-- The head → dependent adjacency: `(edgeDigraph deps).Adj`, i.e. there is an
    edge `(v → w)` in `deps` (see `parentEdge_iff` for the list form). -/
def ParentEdge (deps : List Dependency) : Nat → Nat → Prop :=
  (edgeDigraph deps).Adj

/-- Membership characterization of the adjacency. -/
@[simp] theorem parentEdge_iff {deps : List Dependency} {v w : Nat} :
    ParentEdge deps v w ↔ ∃ d ∈ deps, d.headIdx = v ∧ d.depIdx = w := by
  simp [ParentEdge, edgeDigraph]

instance (deps : List Dependency) : DecidableRel (ParentEdge deps) :=
  inferInstanceAs (DecidableRel
    (Digraph.mk' λ v w => deps.any λ d => d.headIdx == v && d.depIdx == w).Adj)

namespace Graph

/-- The edges into position `i`. -/
def parentsOf (g : Graph) (i : Nat) : List Dependency :=
  g.deps.filter (·.depIdx == i)

/-- The dependent positions of the word at position `i`. -/
def children (g : Graph) (i : Nat) : List Nat :=
  g.deps.filter (·.headIdx == i) |>.map (·.depIdx)

/-- The number of incoming edges at position `i`. -/
def inDegree (g : Graph) (i : Nat) : Nat :=
  (g.parentsOf i).length

/-- The graph's digraph: `edgeDigraph` on its edge list. -/
def toDigraph (g : Graph) : Digraph Nat :=
  edgeDigraph g.deps

@[simp] theorem toDigraph_adj (g : Graph) (v w : Nat) :
    g.toDigraph.Adj v w ↔ ParentEdge g.deps v w := Iff.rfl

/-- More edges, larger digraph: a graph's digraph is a subgraph of any
    enhancement of it (in the `Digraph` lattice order). -/
theorem toDigraph_mono {g g' : Graph} (h : g.deps ⊆ g'.deps) :
    g.toDigraph ≤ g'.toDigraph := λ v w hvw => by
  obtain ⟨d, hd, hh, hdep⟩ := parentEdge_iff.mp hvw
  exact parentEdge_iff.mpr ⟨d, h hd, hh, hdep⟩

attribute [coe] toDigraph

instance : Coe Graph (Digraph Nat) := ⟨toDigraph⟩

end Graph

/-- A dependency tree: a `Graph` meant to be single-headed (`hasUniqueHeads`
    checks it), plus DG-specific lexical argument-structure premises. `frames`
    is aligned with `words` (missing/short = no frame): the frame is framework
    apparatus (like HPSG's ARG-ST), so it lives on DG's tree, not on the shared
    `Word` token; frames come from the lexical carrier at tree construction
    (`complementToArgStr` applied to a verb's `complementType`). -/
structure Tree extends Graph where
  /-- Argument-structure premises aligned with `words`; short or missing list
      means "no frame at this position" (see `Tree.frame`). -/
  frames : List (Option ArgStr) := []
  deriving Repr

/-- The argument-structure frame at position `i`, if one was supplied. -/
def Tree.frame (t : Tree) (i : Nat) : Option ArgStr :=
  (t.frames[i]?).join

end DependenciesAndTrees

section WellFormedness

/-- Check if every word except root has exactly one head. -/
def hasUniqueHeads (t : Tree) : Bool :=
  (List.range t.words.length).all λ i =>
    t.inDegree i == (if i == t.rootIdx then 0 else 1)

/-- Check for cycles: no word is its own ancestor. -/
def isAcyclic (t : Tree) : Bool :=
  let n := t.words.length
  List.range n |>.all λ start =>
    let rec follow (current : Nat) (visited : List Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | fuel' + 1 =>
        if visited.contains current then false
        else
          match t.deps.find? (·.depIdx == current) with
          | some dep => follow dep.headIdx (current :: visited) fuel'
          | none => true
    follow start [] (n + 1)

/-- Bundled well-formedness: unique heads + valid index bounds.
    Collects the three hypotheses that most dominance/planarity theorems need. -/
structure Tree.WF (t : Tree) : Prop where
  uniqueHeads : hasUniqueHeads t = true
  depIdx_lt : ∀ d ∈ t.deps, d.depIdx < t.words.length
  headIdx_lt : ∀ d ∈ t.deps, d.headIdx < t.words.length

end WellFormedness

section AgreementChecking

/-- Number agreement across every `rel`-labeled edge. Permissive by default:
    edges whose endpoints are out of range or unmarked for number pass
    vacuously, so the check constrains only overtly conflicting marking. -/
def numberAgreesOn (t : Tree) (rel : UD.DepRel) : Bool :=
  t.deps.all λ d =>
    if d.depType == rel then
      match t.words[d.depIdx]?, t.words[d.headIdx]? with
      | some dep, some head =>
        match dep.features.number, head.features.number with
        | some dn, some hn => dn == hn
        | _, _ => true
      | _, _ => true
    else true

/-- Subject-verb number agreement: `numberAgreesOn` at `nsubj`. -/
def checkSubjVerbAgr (t : Tree) : Bool := numberAgreesOn t .nsubj

/-- Determiner-noun number agreement: `numberAgreesOn` at `det`. -/
def checkDetNounAgr (t : Tree) : Bool := numberAgreesOn t .det

end AgreementChecking

end DependencyGrammar
