/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Mixed graphs

A **mixed graph** `G = (V, E, A)` has both undirected edges `E` and directed arcs
`A` on one vertex set: a `SimpleGraph` and a `Digraph` bundled over `V`. Mathlib
has both halves but no bundle. Candidate for
`Mathlib/Combinatorics/MixedGraph/Basic.lean`.

## Main definitions

* `MixedGraph V`: the bundle.
* `SimpleGraph.toMixedGraph` / `Digraph.toMixedGraph`: the degenerate cases —
  a simple graph is a mixed graph with no arcs, a digraph one with no edges.
-/

/-- A mixed graph: undirected edges and directed arcs on one vertex type. -/
@[ext]
structure MixedGraph (V : Type*) where
  /-- The undirected edges. -/
  edges : SimpleGraph V
  /-- The directed arcs. -/
  arcs : Digraph V

variable {V : Type*}

/-- A simple graph is a mixed graph with no arcs. -/
def SimpleGraph.toMixedGraph (G : SimpleGraph V) : MixedGraph V := ⟨G, ⊥⟩

/-- A digraph is a mixed graph with no edges. -/
def Digraph.toMixedGraph (D : Digraph V) : MixedGraph V := ⟨⊥, D⟩
