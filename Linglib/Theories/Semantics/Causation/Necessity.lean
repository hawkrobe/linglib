import Linglib.Core.Causal.SEM.Counterfactual

/-!
# Causal Necessity
@cite{nadathur-2024} @cite{nadathur-lauer-2020} @cite{schulz-2011}

Causal necessity semantics for the verb "cause." The core definition
`causallyNecessary` (in `Core.Causal.SEM`) implements
@cite{nadathur-2024} Definition 10b (supersituation necessity:
precondition + achievability + but-for), superseding the simple but-for
test from @cite{nadathur-lauer-2020} Definition 24.

## Insight

"X caused Y" asserts that X was necessary for Y: without X, Y would not
have occurred (counterfactual dependence). X is a but-for cause:
"but for X, not Y."

## Necessity vs Sufficiency

| Verb | Semantics | Test |
|------|-----------|------|
| cause | Necessity (Def 10b) | No consistent supersituation achieves E without C |
| make | Sufficiency (Def 23) | Does adding C guarantee E? |

The legacy `CausalDynamics`-based `causeSem`/`isINUSCause`/
`actuallyCaused` were deleted in Phase D-H. The polymorphic V2 versions
are promoted to canonical here.
-/

namespace Semantics.Causation.Necessity

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- V2 causal-necessity semantics for "cause": setting cause to xC
    develops effect to xE AND cause-as-xC is causally necessary
    (Nadathur 2024 Def 10b) for effect-as-xE. Polymorphic. -/
noncomputable def causeSem {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (cause : V) (xC : α cause) (effect : V) (xE : α effect) : Prop :=
  (M.developDet (background.extend cause xC)).hasValue effect xE ∧
  SEM.causallyNecessary M background cause xC effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (causeSem M bg cause xC effect xE) := Classical.dec _

/-- V2 INUS cause (Mackie): insufficient but necessary part of an
    unnecessary but sufficient condition. Polymorphic. -/
noncomputable def isINUSCause {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (cause : V) (xC : α cause) (effect : V) (xE : α effect)
    (enablingConditions : Valuation α) : Prop :=
  SEM.causallySufficient M enablingConditions cause xC effect xE ∧
  SEM.causallyNecessary M enablingConditions cause xC effect xE ∧
  ¬ SEM.causallySufficient M Valuation.empty cause xC effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (cause : V) (xC : α cause) (effect : V) (xE : α effect)
    (enablingConditions : Valuation α) :
    Decidable (isINUSCause M cause xC effect xE enablingConditions) := Classical.dec _

/-- V2 actual causation: cause factually took value xC, and was causally
    necessary (Def 10b) for effect-as-xE — tested against the actual
    situation with cause stripped from the background. Polymorphic. -/
noncomputable def actuallyCaused {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Prop :=
  s.hasValue cause xC ∧
  causeSem M (s.remove cause) cause xC effect xE

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (s : Valuation α) (cause : V) (xC : α cause) (effect : V) (xE : α effect) :
    Decidable (actuallyCaused M s cause xC effect xE) := Classical.dec _

end Semantics.Causation.Necessity
