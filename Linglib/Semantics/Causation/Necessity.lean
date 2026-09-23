module

public import Linglib.Semantics.Causation.SEM.Entailment

/-!
# Causal necessity: the semantics of *cause*

On the account of [nadathur-lauer-2020], *X caused Y* asserts that X was causally necessary for
Y, where *X made Y happen* asserts sufficiency. `causeSem` states the necessity reading over
the strict development of a structural equation model: given the background, the cause
entails the effect, and the cause is causally necessary for it in the sense of
[nadathur-2023-implicatives]'s Definition 10b (`SEM.causallyNecessary`), which refines the
but-for test of [nadathur-lauer-2020]'s Definition 24.

## References

* [nadathur-lauer-2020]
* [nadathur-2023-implicatives]
* [schulz-2011]
-/

@[expose] public section

namespace Causation.Necessity

open Causation (SEM CausalGraph Valuation DecidableValuation)

variable {V : Type*} {α : V → Type*} [Fintype V] [DecidableEq V] [DecidableValuation α]
  [∀ v, Fintype (α v)] (M : SEM V α) [CausalGraph.IsDAG M.graph]

/-- *cause*: setting the cause to `xC` causally entails the effect `xE`, and the cause is
causally necessary for the effect (Definition 10b). -/
def causeSem (background : Valuation α)
    (cause : V) (xC : α cause) (effect : V) (xE : α effect) : Prop :=
  SEM.causallyEntails M (background.extend cause xC) effect xE ∧
  SEM.causallyNecessary M background cause xC effect xE

instance (bg : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causeSem M bg cause xC effect xE) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Causation.Necessity
