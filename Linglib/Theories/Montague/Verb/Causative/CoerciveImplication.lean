/-
# Coercive Implication

The coercive interpretation of "make" with volitional causees,
based on Nadathur & Lauer (2020).

## Key Insight

When "X made Y do Z" involves a volitional action Z:
- The causee (Y) could have chosen otherwise
- But X's action **determined** the outcome
- Implication: Y didn't freely choose Z; Y was coerced

## Examples

1. "Kim made Sandy leave"
   - Leaving is a volitional action (Sandy could choose to stay)
   - Kim's action made leaving inevitable
   - Coercive implication: Sandy didn't want to leave, or Sandy was forced

2. "The rain made me stay inside"
   - Staying inside is volitional (I could have gone out anyway)
   - The rain made staying the determined outcome
   - Coercive implication: I would have preferred to go out

3. "Kim made Sandy sneeze" (less natural)
   - Sneezing is NOT volitional
   - No coercive implication (you can't coerce an involuntary action)
   - This is why "make + sneeze" sounds odd without special context

## Formal Analysis

The coercive implication arises from:
1. Sufficiency: the cause determined the effect
2. Volitionality: the effect was (in principle) under the causee's control
3. Pragmatic inference: if it was under their control but determined, they must
   have been overridden

## References

- Nadathur & Lauer (2020), Section 6
- Talmy (1988). Force dynamics in language and cognition.
-/

import Linglib.Theories.Montague.Verb.Causative.Sufficiency
import Linglib.Theories.Montague.Verb.Causative.Necessity

namespace Theories.NadathurLauer2020.CoerciveImplication

open Theories.Montague.Conditional.CausalModel
open Theories.NadathurLauer2020.Sufficiency

-- Volitionality

/--
**Action Type**: Classifies actions by their volitionality.

- Volitional: under the agent's control (leaving, eating, speaking)
- NonVolitional: not under control (sneezing, dying, falling)
- Ambiguous: depends on context (crying can be controlled or not)
-/
inductive ActionType
  | Volitional
  | NonVolitional
  | Ambiguous
  deriving DecidableEq, Repr, BEq, Inhabited

/--
An event with its associated volitionality.
-/
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

-- Coercive Implication

/--
**Coercive Context**: A situation where "make" creates coercive implication.

"X made Y do Z" has a coercive reading when:
1. Z is a volitional action (Y could choose otherwise)
2. X's action was sufficient for Z (Z was determined)
3. Inference: Y's choice was overridden
-/
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

/--
**Has Coercive Implication**: Check if the context generates coercion inference.

Coercive implication arises when:
1. The causee's action is volitional
2. The causer's action was sufficient for the causee's action
-/
def hasCoerciveImplication (ctx : CoerciveContext) : Bool :=
  ctx.causeeAction.isVolitional &&
  causallySufficient ctx.dynamics ctx.background ctx.causerAction ctx.causeeAction.event

/--
**Coercion Strength**: How strongly does the context imply coercion?

- Strong: volitional action + sufficient cause
- Weak: ambiguous volitionality + sufficient cause
- None: non-volitional action (coercion doesn't apply)
-/
inductive CoercionStrength
  | Strong
  | Weak
  | None
  deriving DecidableEq, Repr, BEq

/--
Compute the coercion strength of a context.
-/
def coercionStrength (ctx : CoerciveContext) : CoercionStrength :=
  if !causallySufficient ctx.dynamics ctx.background ctx.causerAction ctx.causeeAction.event then
    .None  -- Sufficiency required for coercion
  else match ctx.causeeAction.actionType with
    | .Volitional => .Strong
    | .Ambiguous => .Weak
    | .NonVolitional => .None

end CoerciveContext

-- Make vs Cause with Volitionality

/--
**Make with Volitional Effect**: The canonical coercive construction.

"Kim made Sandy leave" where leaving is volitional.
-/
def makeVolitional (dyn : CausalDynamics) (background : Situation)
    (causer _causee : Variable) (effect : TaggedEvent) : Bool :=
  effect.isVolitional &&
  makeSem dyn background causer effect.event

/--
**Cause with Volitional Effect**: Less coercive than "make".

"Kim caused Sandy to leave" - suggests Kim's action led to leaving,
but with more agency for Sandy.
-/
def causeVolitional (dyn : CausalDynamics) (background : Situation)
    (causer _causee : Variable) (effect : TaggedEvent) : Bool :=
  Necessity.causeSem dyn background causer effect.event

-- The Coercion Inference Chain

/--
**Presupposition**: The causee had the capacity to do otherwise.

For coercion to make sense, the causee must have been able to resist.
This is presupposed by volitional "make".
-/
def presupposeCapacity (effect : TaggedEvent) : Bool :=
  effect.actionType == .Volitional || effect.actionType == .Ambiguous

/--
**Inference**: The causee's preference was overridden.

Given:
1. The action was volitional (causee could choose)
2. The cause was sufficient (action was determined)

Infer:
- The causee would have chosen differently without the cause
- The cause "overrode" the causee's autonomous choice
-/
def inferOverriddenPreference (ctx : CoerciveContext) : Bool :=
  presupposeCapacity ctx.causeeAction &&
  ctx.hasCoerciveImplication

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

-- Connection to Causative Verb Choice

/--
**Verb Choice and Coercion**: Why speakers choose "make" vs "cause".

"Make" is preferred when:
1. The speaker wants to emphasize the sufficiency of the cause
2. The effect is volitional (creating coercive implication)
3. The speaker views the causee's agency as overridden

"Cause" is preferred when:
1. The speaker wants to emphasize the necessity of the cause
2. The effect may not be volitional
3. The speaker views the causee as having some agency
-/
structure CausativeChoice where
  /-- Does the speaker want to emphasize sufficiency? -/
  emphasizeSufficiency : Bool
  /-- Does the speaker want to imply coercion? -/
  implyCoercion : Bool
  /-- Is the effect clearly volitional? -/
  effectVolitional : Bool
  deriving Repr

/--
Recommend which verb to use based on the context.
-/
def recommendVerb (choice : CausativeChoice) : String :=
  if choice.implyCoercion && choice.effectVolitional then
    "make"  -- Coercion + volitional → "make"
  else if choice.emphasizeSufficiency then
    "make"  -- Emphasize guarantee → "make"
  else
    "cause"  -- Default to "cause" for necessity

end Theories.NadathurLauer2020.CoerciveImplication
