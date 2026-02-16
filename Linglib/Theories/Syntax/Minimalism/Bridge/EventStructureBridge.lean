import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Theories.Semantics.Events.EventStructure

/-!
# Event Structure ↔ Syntactic Heads Bridge

Connects Rappaport Hovav & Levin's (1998) event structure templates to
Cuervo's (2003) syntactic verb head decomposition. This bridges the
semantic layer (EventSemantics/EventStructure) to the syntactic layer
(Minimalism/Core/Applicative).

## Key Mapping

| Template         | VerbHeads      | Description                    |
|-----------------|----------------|--------------------------------|
| state           | [vBE]          | Simple state                   |
| activity        | [vDO]          | Agentive activity              |
| achievement     | [vGO, vBE]     | Inchoative change of state     |
| accomplishment  | [vDO, vGO, vBE]| Causative with external cause  |
| motionContact   | [vDO]          | Manner activity (MOVE+CONTACT) |

## References

- Rappaport Hovav, M. & Levin, B. (1998). Building verb meanings.
- Cuervo, M. C. (2003). Datives at Large. PhD dissertation, MIT.
-/

namespace Minimalism.Bridge

open EventSemantics.EventStructure
open Minimalism

-- ============================================================================
-- § 1: Template → VerbHead Mapping
-- ============================================================================

/-- Map event structure templates to Cuervo's verb head decomposition.

    This is the core syntax–semantics bridge: the semantic template
    determines which sub-eventive heads are projected in the syntax. -/
def templateToHeads : Template → List VerbHead
  | .state          => [.vBE]
  | .activity       => [.vDO]
  | .achievement    => [.vGO, .vBE]
  | .accomplishment => [.vDO, .vGO, .vBE]
  | .motionContact  => [.vDO]  -- Manner activity (R&L 2024)

-- ============================================================================
-- § 2: Bridge Theorems
-- ============================================================================

/-- Accomplishments map to causative structure. -/
theorem accomplishment_is_causative :
    isCausative (templateToHeads .accomplishment) = true := by native_decide

/-- Achievements map to inchoative structure. -/
theorem achievement_is_inchoative :
    isInchoative (templateToHeads .achievement) = true := by native_decide

/-- States map to simple state structure. -/
theorem state_maps_to_state :
    isState (templateToHeads .state) = true := by native_decide

/-- Activities map to simple activity structure. -/
theorem activity_maps_to_activity :
    isActivity (templateToHeads .activity) = true := by native_decide

/-- Accomplishments have external cause iff they have vDO. -/
theorem accomplishment_has_external_cause :
    Template.hasExternalCauser .accomplishment = true ∧
    (templateToHeads .accomplishment).contains .vDO = true := ⟨rfl, by native_decide⟩

/-- Achievements lack external cause and lack vDO. -/
theorem achievement_no_external_cause :
    Template.hasExternalCauser .achievement = false ∧
    (templateToHeads .achievement).contains .vDO = false := ⟨rfl, by native_decide⟩

/-- The causative alternation: accomplishment and achievement share the
    inchoative core [vGO, vBE], differing only in vDO (external cause). -/
theorem causative_alternation_shared_core :
    let accHeads := templateToHeads .accomplishment
    let achHeads := templateToHeads .achievement
    achHeads.all (accHeads.contains ·) = true := by native_decide

end Minimalism.Bridge
