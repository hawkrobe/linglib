/-!
# Positions in a two-link causal chain

A causal chain runs from a causing subevent to a caused one, and a language's linking rules can
read a participant's place in that chain ([croft-2012], [talmy-1988]). This file holds the two
positions of the minimal such chain, shared by the analyses that project thematic hierarchies or
argument marking off it.

Finer localist scales, on which a participant sits at a graded distance along the chain, are a
different classification and belong with the accounts that use them.

## Main definitions

* `CausalChainPosition` — the causing and caused ends of a two-link chain
-/

namespace Causation

/-- Position in a two-link causal chain: the causing subevent that opens it and the caused
subevent that closes it. -/
inductive CausalChainPosition where
  /-- The causing subevent — a percept, an event, or an instigating process. -/
  | onset
  /-- The caused subevent — the state change or mental state the chain terminates in. -/
  | terminus
  deriving DecidableEq, Repr

end Causation
