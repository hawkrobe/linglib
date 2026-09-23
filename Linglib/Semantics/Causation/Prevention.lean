module

public import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Prevention: the semantics of *prevent*

`preventSem` states the behavioural reading of *prevent* after
[sloman-barbey-hotaling-2009]: setting the preventer to `xPrev` does not suffice for the effect,
while some other value of the preventer does. With Bool models and `xPrev = true`, the only
alternative is `false`. The predicate takes the same arguments as the other causative
semantics, so `Causative.toSemantics` dispatches uniformly.

## References

* [sloman-barbey-hotaling-2009]
-/

@[expose] public section

namespace Causation.Prevention

open Causation (SEM CausalGraph Valuation DecidableValuation)

/-- *prevent*: setting the preventer to `xPrev` does not suffice for `effect = xE`, and some
other value of the preventer does. -/
def preventSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (bg : Valuation α)
    (preventer : V) (xPrev : α preventer)
    (effect : V) (xE : α effect) : Prop :=
  ¬ SEM.causallySufficient M bg preventer xPrev effect xE ∧
  ∃ xPrev_alt : α preventer, xPrev_alt ≠ xPrev ∧
    SEM.causallySufficient M bg preventer xPrev_alt effect xE

instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph]
    (bg : Valuation α) (preventer : V) (xP : α preventer)
    (effect : V) (xE : α effect) :
    Decidable (preventSem M bg preventer xP effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Causation.Prevention
