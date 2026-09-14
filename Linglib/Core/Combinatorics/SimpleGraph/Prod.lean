import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Decidable adjacency in a box product

The adjacency of a box product of two graphs with decidable adjacency and decidable vertex
equality is decidable.
-/

namespace SimpleGraph

variable {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}

instance [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj :=
  λ _ _ => decidable_of_iff _ boxProd_adj.symm

end SimpleGraph
