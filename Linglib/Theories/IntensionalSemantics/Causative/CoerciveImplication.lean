/-
# Coercive Implication (Nadathur & Lauer 2020 §6)

"X made Y do Z" with volitional Z implies coercion: sufficiency
(Z was determined) + volitionality (Y could choose otherwise) →
Y's choice was overridden.
-/

import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency
import Linglib.Theories.IntensionalSemantics.Causative.Necessity

namespace Theories.NadathurLauer2020.CoerciveImplication

open Core.CausalModel
open Theories.NadathurLauer2020.Sufficiency

/-- Action volitionality (volitional/non-volitional/ambiguous). -/
inductive ActionType
  | Volitional
  | NonVolitional
  | Ambiguous
  deriving DecidableEq, Repr, BEq, Inhabited

/-- An event tagged with volitionality. -/
structure TaggedEvent where
  event : Variable
  actionType : ActionType
  deriving Repr

namespace TaggedEvent

/-- Create a volitional event -/
def volitional (v : Variable) : TaggedEvent :=
  { event := v, actionType := .Volitional }

/-- Create a non-volitional event -/
def nonVolitional (v : Variable) : TaggedEvent :=
  { event := v, actionType := .NonVolitional }

/-- Check if an event is volitional -/
def isVolitional (te : TaggedEvent) : Bool :=
  te.actionType == .Volitional

end TaggedEvent

/-- A situation where "make" creates coercive implication. -/
structure CoerciveContext where
  /-- The causal dynamics -/
  dynamics : CausalDynamics
  /-- The background situation -/
  background : Situation
  /-- The causer's action -/
  causerAction : Variable
  /-- The causee's action (the effect) -/
  causeeAction : TaggedEvent

namespace CoerciveContext

/-- Coercion arises when effect is volitional and cause is sufficient. -/
def hasCoerciveImplication (ctx : CoerciveContext) : Bool :=
  ctx.causeeAction.isVolitional &&
  causallySufficient ctx.dynamics ctx.background ctx.causerAction ctx.causeeAction.event

/-- Coercion strength: strong (volitional), weak (ambiguous), none. -/
inductive CoercionStrength
  | Strong
  | Weak
  | None
  deriving DecidableEq, Repr, BEq

/-- Compute coercion strength. -/
def coercionStrength (ctx : CoerciveContext) : CoercionStrength :=
  if !causallySufficient ctx.dynamics ctx.background ctx.causerAction ctx.causeeAction.event then
    .None  -- Sufficiency required for coercion
  else match ctx.causeeAction.actionType with
    | .Volitional => .Strong
    | .Ambiguous => .Weak
    | .NonVolitional => .None

end CoerciveContext

-- Examples

section Examples

/-- Kim (causer) -/
def kim : Variable := mkVar "kim_acts"

/-- Sandy (causee) -/
def sandy : Variable := mkVar "sandy"

/-- Sandy leaving (volitional) -/
def sandyLeaves : TaggedEvent :=
  TaggedEvent.volitional (mkVar "sandy_leaves")

/-- Sandy sneezing (non-volitional) -/
def sandySneezes : TaggedEvent :=
  TaggedEvent.nonVolitional (mkVar "sandy_sneezes")

/--
Dynamics where Kim's action causes Sandy to leave.
-/
def kimSandyDynamics : CausalDynamics :=
  ⟨[CausalLaw.simple kim sandyLeaves.event]⟩

/--
**"Kim made Sandy leave"** - has coercive implication.

Kim's action was sufficient + Sandy leaving is volitional
→ Sandy was coerced (didn't freely choose to leave)
-/
theorem kim_sandy_coercive :
    let ctx : CoerciveContext := {
      dynamics := kimSandyDynamics
      background := Situation.empty
      causerAction := kim
      causeeAction := sandyLeaves
    }
    ctx.hasCoerciveImplication = true := by
  native_decide

/--
Dynamics where Kim causes Sandy to sneeze (odd construction).
-/
def kimSneezeDynamics : CausalDynamics :=
  ⟨[CausalLaw.simple kim sandySneezes.event]⟩

/--
**"Kim made Sandy sneeze"** - NO coercive implication.

Kim's action was sufficient, but sneezing is non-volitional
→ No coercion inference (you can't override an involuntary action)
-/
theorem kim_sneeze_not_coercive :
    let ctx : CoerciveContext := {
      dynamics := kimSneezeDynamics
      background := Situation.empty
      causerAction := kim
      causeeAction := sandySneezes
    }
    ctx.hasCoerciveImplication = false := by
  native_decide

/--
**Coercion strength is strong for volitional actions**.
-/
theorem coercion_strong_volitional :
    let ctx : CoerciveContext := {
      dynamics := kimSandyDynamics
      background := Situation.empty
      causerAction := kim
      causeeAction := sandyLeaves
    }
    ctx.coercionStrength = .Strong := by
  native_decide

/--
**Coercion strength is none for non-volitional actions**.
-/
theorem coercion_none_nonvolitional :
    let ctx : CoerciveContext := {
      dynamics := kimSneezeDynamics
      background := Situation.empty
      causerAction := kim
      causeeAction := sandySneezes
    }
    ctx.coercionStrength = .None := by
  native_decide

end Examples

end Theories.NadathurLauer2020.CoerciveImplication
