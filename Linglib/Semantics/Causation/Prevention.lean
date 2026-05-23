import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Prevention Semantics
@cite{sloman-barbey-hotaling-2009}

`preventSem` formalizes the SEM semantics of "prevent": the preventer
blocks an effect that would otherwise occur. Behavioral, not structural:
setting `preventer := xPrev` blocks `effect = xE`, AND there exists some
alternative preventer value that would have allowed `effect = xE` to
develop.

Bool models recover the standard "false vs true" flip via the
`∃ xPrev_alt ≠ xPrev` clause (with `xPrev = true`, the only alternative
is `false`).

The legacy structural `preventSem` over `CausalDynamics` (which
introspected an inhibitory law's structure rather than checking
behavior) was deleted in Phase D-H. The behavioral V2 form here is
arity-uniform with `causallySufficient`/`causeSem` so `Causative.toSemantics`
dispatches uniformly across all five force-dynamic variants.
-/

namespace Semantics.Causation.Prevention

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- V2 prevention semantics: preventer-as-`xPrev` blocks effect-from-
    being-`xE`, AND there exists some alternative preventer value that
    would have allowed `effect = xE` to develop. Polymorphic over
    value types. -/
noncomputable def preventSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α)
    (preventer : V) (xPrev : α preventer)
    (effect : V) (xE : α effect) : Prop :=
  ¬ (M.developDet (bg.extend preventer xPrev)).hasValue effect xE ∧
  ∃ xPrev_alt : α preventer, xPrev_alt ≠ xPrev ∧
    (M.developDet (bg.extend preventer xPrev_alt)).hasValue effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α) (preventer : V) (xP : α preventer)
    (effect : V) (xE : α effect) :
    Decidable (preventSem M bg preventer xP effect xE) := Classical.dec _

end Semantics.Causation.Prevention
