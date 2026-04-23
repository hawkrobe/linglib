import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Coercive Implication (@cite{nadathur-lauer-2020})

"X made Y do Z" with volitional Z implies coercion: sufficiency
(Z was determined) + volitionality (Y could choose otherwise) →
Y's choice was overridden.

The legacy `CausalDynamics`-based `CoerciveContext` + Kim/Sandy
examples were deleted in Phase D-H. The polymorphic V2
`hasCoerciveImplication` is promoted to canonical here.
-/

namespace Semantics.Causation.CoerciveImplication

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)

/-- Action volitionality (volitional/non-volitional/ambiguous). -/
inductive ActionType
  | Volitional
  | NonVolitional
  | Ambiguous
  deriving DecidableEq, Repr, Inhabited

/-- Coercion strength: strong (volitional), weak (ambiguous), none. -/
inductive CoercionStrength
  | Strong
  | Weak
  | None
  deriving DecidableEq, Repr

/-- V2 coercive implication: causer's action-as-`xCauser` is causally
    sufficient for a volitional causee action-as-`xEvent`. Polymorphic. -/
noncomputable def hasCoerciveImplication {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (background : Valuation α)
    (causerAction : V) (xCauser : α causerAction)
    (causeeIsVolitional : Bool)
    (causeeEvent : V) (xEvent : α causeeEvent) : Prop :=
  causeeIsVolitional = true ∧
  SEM.causallySufficient M background causerAction xCauser causeeEvent xEvent

noncomputable instance {V : Type*} {α : V → Type*}
    [Fintype V] [DecidableEq V] [DecidableValuation α]
    (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (bg : Valuation α) (causer : V) (xC : α causer) (vol : Bool)
    (effect : V) (xE : α effect) :
    Decidable (hasCoerciveImplication M bg causer xC vol effect xE) := Classical.dec _

end Semantics.Causation.CoerciveImplication
