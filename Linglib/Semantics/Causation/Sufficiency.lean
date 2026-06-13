import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Causal Sufficiency
[nadathur-lauer-2020] [schulz-2011]

Causal sufficiency semantics for the verb "make" based on
[nadathur-lauer-2020] Definition 23.

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
study files (e.g., `Levin2026.HammerFlat`).
-/

namespace Causation.Sufficiency

open Causation (SEM CausalGraph Valuation DecidableValuation)

/-- V2 sufficiency for "make" ([nadathur-lauer-2020] Definition 23, both
    clauses, over the strict T_D development):

    - **(a) non-inevitability**: the development of `background` does not
      already fix `effect = xE`;
    - **(b) sufficiency**: the development of `background + (cause = xC)`
      fixes `effect = xE`.

    Bool models pass `xC = xE = true` at the call site. The bare
    clause-(b)-only predicate (over the eager-total development) remains
    available as `SEM.causallySufficient`. -/
def makeSem {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V]
    [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (cause : V) (xC : α cause) (effect : V) (xE : α effect) : Prop :=
  ¬ SEM.causallyEntails M background effect xE ∧
  SEM.causallyEntails M (background.extend cause xC) effect xE

noncomputable instance {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V]
    [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (makeSem M background cause xC effect xE) := Classical.dec _

end Causation.Sufficiency
