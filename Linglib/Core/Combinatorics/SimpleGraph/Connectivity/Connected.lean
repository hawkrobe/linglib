module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Neighbours in a preconnected induced subgraph

A vertex of a nontrivial set inducing a preconnected subgraph has a neighbour in the set: the
form of `SimpleGraph.Preconnected.exists_adj_of_nontrivial` for induced subgraphs, stated on
the ambient graph.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s : Set V} {v : V}

/-- Every vertex of a nontrivial set inducing a preconnected subgraph has a neighbour in the
set. -/
theorem Preconnected.exists_adj_mem_of_nontrivial (h : (G.induce s).Preconnected)
    (hs : s.Nontrivial) (hv : v ∈ s) : ∃ w ∈ s, G.Adj v w :=
  have := hs.coe_sort
  let ⟨w, hw⟩ := h.exists_adj_of_nontrivial ⟨v, hv⟩
  ⟨w, w.2, hw⟩

end SimpleGraph
