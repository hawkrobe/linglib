module

public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Decidable adjacency in a box product

`[UPSTREAM]` candidate for `Mathlib/Combinatorics/SimpleGraph/Prod.lean`: the adjacency of a box
product of two graphs with decidable adjacency and decidable vertex equality is decidable.
-/

@[expose] public section

namespace SimpleGraph

variable {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}

instance [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj :=
  fun _ _ ↦ decidable_of_iff' _ boxProd_adj

end SimpleGraph
