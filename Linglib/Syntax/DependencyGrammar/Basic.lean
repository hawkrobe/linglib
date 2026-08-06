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
* `Graph.parents`, `children`, `inDegree` — the local graph API.
* `Graph.IsTree` — the graph is a dependency tree (single-headed, acyclic);
  tree-hood is a property of a graph, not a separate structure.

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

/-! ### Well-formedness -/

section WellFormedness

variable {n : ℕ}

/-- Every position except the root has exactly one head, and the root none. -/
def hasUniqueHeads (t : Graph n) : Bool :=
  (List.finRange n).all λ i =>
    t.inDegree i == (if i == t.root then 0 else 1)

/-- No position is its own ancestor: following heads from any position
    terminates without revisiting. -/
def isAcyclic (t : Graph n) : Bool :=
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

/-- The graph is a dependency tree: single-headed and acyclic. On `Fin n`
    these two imply rootedness and connectivity — every non-root position's
    head chain terminates at the unique in-degree-0 position, the root. -/
structure Graph.IsTree (t : Graph n) : Prop where
  uniqueHeads : hasUniqueHeads t = true
  acyclic : isAcyclic t = true

end WellFormedness

/-! ### Agreement -/

section AgreementChecking

variable {n : ℕ}

/-- Number agreement across every `rel`-labeled arc. Permissive by default:
    arcs whose endpoints are unmarked for number pass vacuously, so the check
    constrains only overtly conflicting marking. -/
def numberAgreesOn (t : Graph n) (rel : UD.DepRel) : Bool :=
  (List.finRange n).all λ v => (List.finRange n).all λ w =>
    if t.label v w == some rel then
      match (t.words w).features.number, (t.words v).features.number with
      | some dn, some hn => dn == hn
      | _, _ => true
    else true

/-- Subject-verb number agreement: `numberAgreesOn` at `nsubj`. -/
def checkSubjVerbAgr (t : Graph n) : Bool := numberAgreesOn t .nsubj

/-- Determiner-noun number agreement: `numberAgreesOn` at `det`. -/
def checkDetNounAgr (t : Graph n) : Bool := numberAgreesOn t .det

end AgreementChecking

end DependencyGrammar
