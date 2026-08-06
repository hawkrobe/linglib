import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Linglib.Data.UD.Basic
import Linglib.Morphology.Word.Basic

/-!
# Dependency grammar substrate

The dependency structure of a sentence, in the carrier of the formal
dependency-grammar literature ([kuhlmann-nivre-2006], [kuhlmann-2013];
the arcs-among-ordered-words presentation goes back to [melcuk-1988]): the
nodes are the sentence positions `Fin n` with their linear order, and the
arcs are a labeling of ordered pairs of positions by UD v2 dependency
relations (`Data/UD/Basic.lean`). A distinguished `root` replaces CoNLL-U's
artificial root token, following [kuhlmann-nivre-2006].

## Main declarations

* `Graph n` — a dependency graph on `n` words: vertex-labeling `words`,
  arc-labeling `label`, distinguished `root`. `Graph.Adj` is the induced
  adjacency (decidable), `Graph.toDigraph` the projection onto mathlib's
  `Digraph`, and `Graph.ofArcs` the constructor from CoNLL-U-style arc
  lists.
* `Tree n` — a `Graph n` with argument-structure frames, intended
  single-headed (`hasUniqueHeads` checks it; see `Tree.WF`).
* `Graph.parents`, `children`, `inDegree` — the local graph API.

## Implementation notes

* Positions are 0-indexed; CoNLL-U is 1-indexed with `0` as an artificial
  root, so wire-format conversion shifts indices.
* `label` returns at most one relation per ordered pair: faithful to
  dependency trees and basic UD. If an enhanced-UD fixture ever needs
  parallel arcs on one pair, the field generalizes to a list.
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

/-! ### Dependency graphs -/

/-- A dependency graph on `n` words: the sentence's tokens as a labeling of
    the positions `Fin n`, the arcs as a partial labeling of ordered position
    pairs (head → dependent) by UD relations, and a distinguished root
    position. -/
structure Graph (n : ℕ) where
  /-- The token at each position. -/
  words : Fin n → Word
  /-- The UD relation from head `v` to dependent `w`, if there is an arc. -/
  label : Fin n → Fin n → Option UD.DepRel
  /-- The root position. -/
  root : Fin n

namespace Graph

variable {n : ℕ} (g : Graph n)

/-- Adjacency: there is an arc from head `v` to dependent `w`. -/
def Adj (v w : Fin n) : Prop := (g.label v w).isSome

instance : DecidableRel g.Adj := λ _ _ => inferInstanceAs (Decidable (_ = true))

/-- The graph as a mathlib `Digraph` on positions. -/
def toDigraph : Digraph (Fin n) := ⟨g.Adj⟩

@[simp] theorem toDigraph_adj (v w : Fin n) : g.toDigraph.Adj v w ↔ g.Adj v w :=
  Iff.rfl

attribute [coe] toDigraph

instance : Coe (Graph n) (Digraph (Fin n)) := ⟨toDigraph⟩

/-- Fewer arcs, smaller digraph, in the `Digraph` lattice order. -/
theorem toDigraph_mono {g g' : Graph n} (h : ∀ v w, g.Adj v w → g'.Adj v w) :
    g.toDigraph ≤ g'.toDigraph := h

/-- The head positions of `w`. -/
def parents (w : Fin n) : List (Fin n) :=
  (List.finRange n).filter (g.Adj · w)

/-- The dependent positions of `v`. -/
def children (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (g.Adj v ·)

/-- The number of incoming arcs at `w`. -/
def inDegree (w : Fin n) : Nat := (g.parents w).length

/-- Build a graph from CoNLL-U-style data: the token list (whose length
    fixes `n`), the root position, and the arcs as
    (head, dependent, relation) triples. Later arcs for the same pair are
    ignored. -/
def ofArcs (words : List Word) (root : Fin words.length)
    (arcs : List (Fin words.length × Fin words.length × UD.DepRel)) :
    Graph words.length :=
  { words := words.get
    label := λ v w => (arcs.find? λ a => a.1 == v && a.2.1 == w).map (·.2.2)
    root }

end Graph

/-! ### Dependency trees -/

/-- A dependency tree: a `Graph n` meant to be single-headed
    (`hasUniqueHeads` checks it; `Tree.WF` bundles the well-formedness),
    plus DG-specific lexical argument-structure premises at each position.
    The frame is framework apparatus (like HPSG's ARG-ST), so it lives on
    DG's tree, not on the shared `Word` token; frames come from the lexical
    carrier at tree construction (`complementToArgStr` applied to a verb's
    `complementType`). -/
structure Tree (n : ℕ) extends Graph n where
  /-- The argument-structure premise at each position, if any. -/
  frames : Fin n → Option ArgStr := λ _ => none

namespace Tree

variable {n : ℕ} (t : Tree n)

/-- Build a tree from CoNLL-U-style data plus a sparse frame table (positions
    not listed carry no frame). -/
def ofArcs (words : List Word) (root : Fin words.length)
    (arcs : List (Fin words.length × Fin words.length × UD.DepRel))
    (frames : List (Fin words.length × ArgStr) := []) : Tree words.length :=
  { Graph.ofArcs words root arcs with
    frames := λ i => (frames.find? (·.1 == i)).map (·.2) }

/-- The argument-structure frame at position `i`, if one was supplied. -/
def frame (i : Fin n) : Option ArgStr := t.frames i

end Tree

/-! ### Well-formedness -/

section WellFormedness

variable {n : ℕ}

/-- Every position except the root has exactly one head, and the root none. -/
def hasUniqueHeads (t : Tree n) : Bool :=
  (List.finRange n).all λ i =>
    t.inDegree i == (if i == t.root then 0 else 1)

/-- No position is its own ancestor: following heads from any position
    terminates without revisiting. -/
def isAcyclic (t : Tree n) : Bool :=
  (List.finRange n).all λ start =>
    let rec follow (current : Fin n) (visited : List (Fin n)) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | fuel' + 1 =>
        if visited.contains current then false
        else
          match (t.parents current).head? with
          | some p => follow p (current :: visited) fuel'
          | none => true
    follow start [] (n + 1)

/-- Bundled well-formedness: the tree really is a rooted tree. -/
structure Tree.WF (t : Tree n) : Prop where
  uniqueHeads : hasUniqueHeads t = true
  acyclic : isAcyclic t = true

end WellFormedness

/-! ### Agreement -/

section AgreementChecking

variable {n : ℕ}

/-- Number agreement across every `rel`-labeled arc. Permissive by default:
    arcs whose endpoints are unmarked for number pass vacuously, so the check
    constrains only overtly conflicting marking. -/
def numberAgreesOn (t : Tree n) (rel : UD.DepRel) : Bool :=
  (List.finRange n).all λ v => (List.finRange n).all λ w =>
    if t.label v w == some rel then
      match (t.words w).features.number, (t.words v).features.number with
      | some dn, some hn => dn == hn
      | _, _ => true
    else true

/-- Subject-verb number agreement: `numberAgreesOn` at `nsubj`. -/
def checkSubjVerbAgr (t : Tree n) : Bool := numberAgreesOn t .nsubj

/-- Determiner-noun number agreement: `numberAgreesOn` at `det`. -/
def checkDetNounAgr (t : Tree n) : Bool := numberAgreesOn t .det

end AgreementChecking

end DependencyGrammar
