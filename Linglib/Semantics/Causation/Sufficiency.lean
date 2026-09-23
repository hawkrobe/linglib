module

public import Linglib.Semantics.Causation.SEM.Counterfactual

/-!
# Causal sufficiency: the semantics of *make*

On the account of [nadathur-lauer-2020], *X made Y happen* asserts that X was causally sufficient
for Y. `makeSem` is their Definition 23 over the strict development of a structural equation
model: the background alone does not entail the effect, and the background together with the
cause does. Bool models pass `xC = xE = true`.

## References

* [nadathur-lauer-2020]
* [schulz-2011]
-/

@[expose] public section

namespace Causation.Sufficiency

open Causation (SEM CausalGraph Valuation DecidableValuation)

/-- Sufficiency for *make* ([nadathur-lauer-2020] Definition 23, both
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
