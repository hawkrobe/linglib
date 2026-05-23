import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Causal Sufficiency
@cite{nadathur-lauer-2020} @cite{schulz-2011}

Causal sufficiency semantics for the verb "make" based on
@cite{nadathur-lauer-2020} Definition 23.

## Insight

"X made Y happen" asserts that X was **sufficient** for Y:
given the background situation, adding X guarantees Y. The effect is
inevitable once the cause is in place.

## Formalization

`makeSem` is a polymorphic alias of `SEM.causallySufficient` over the
V2 `SEM V α` substrate. Bool models pass `xC = xE = true` at the call
site; multi-valued models supply genuine values.

The legacy `CausalDynamics`-based `makeSem` (with `disjunctive_each_sufficient`,
`conjunctive_neither_sufficient_alone`, `conjunctive_sufficient_with_other`
helper theorems over `applyLawsOnce`) was deleted in Phase D-H. The
qualitative claims are recoverable via concrete `BoolSEM` models in
study files (e.g., `Resultatives.HammerFlat`).
-/

namespace Semantics.Causation.Sufficiency

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- V2 sufficiency for "make": setting `cause := xC` develops `effect = xE`.
    Polymorphic over the value type `α`. Bool models pass `xC = xE = true`
    at the call site. Alias of `SEM.causallySufficient`. -/
abbrev makeSem {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V]
    [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (cause : V) (xC : α cause) (effect : V) (xE : α effect) : Prop :=
  SEM.causallySufficient M background cause xC effect xE

end Semantics.Causation.Sufficiency
