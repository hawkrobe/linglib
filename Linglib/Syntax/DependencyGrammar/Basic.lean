import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Basic
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
  `Digraph`, `Linked` / `Graph.toSimpleGraph` its symmetrization (mathlib
  `SimpleGraph`), and `Graph.ofArcs` the constructor from CoNLL-U-style
  arc lists.
* `Graph.parents`, `children`, `inDegree` — the local graph API.
* Well-formedness (`Graph.IsTree`) lives in `Projection.lean`, beside the
  dominance relation it is stated through. Feature-level constraints
  (agreement) are `Syntax/Agreement/`'s domain, not the carrier's.

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

/-- The graph's undirected view: mathlib's orientation-forgetting
    `Digraph.toSimpleGraphInclusive` applied to `toDigraph`. Planarity and
    catena connectivity are stated through it. -/
def toSimpleGraph : SimpleGraph (Fin n) := g.toDigraph.toSimpleGraphInclusive

instance : DecidableRel g.toSimpleGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel g.Adj).Adj)

/-- The head positions of `w`. -/
def parents (w : Fin n) : List (Fin n) :=
  (List.finRange n).filter (g.Adj · w)

/-- The dependent positions of `v`. -/
def children (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (g.Adj v ·)

/-- The number of incoming arcs at `w`. -/
def inDegree (w : Fin n) : Nat := (g.parents w).length

@[simp] theorem mem_parents {g : Graph n} {v w : Fin n} :
    v ∈ g.parents w ↔ g.Adj v w := by
  simp [parents, List.mem_filter]

@[simp] theorem mem_children {g : Graph n} {v w : Fin n} :
    w ∈ g.children v ↔ g.Adj v w := by
  simp [children, List.mem_filter]

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

/-- Positions linked by an arc in either direction — the unbundled adjacency
    of `Graph.toSimpleGraph`, without its `≠` guard. -/
def Linked {n : ℕ} (g : Graph n) (a b : Fin n) : Prop := g.Adj a b ∨ g.Adj b a

instance {n : ℕ} (g : Graph n) (a b : Fin n) : Decidable (Linked g a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem Graph.toSimpleGraph_adj {n : ℕ} (g : Graph n) (v w : Fin n) :
    g.toSimpleGraph.Adj v w ↔ v ≠ w ∧ Linked g v w := Iff.rfl

end DependencyGrammar
