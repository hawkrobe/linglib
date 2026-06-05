import Linglib.Semantics.Events.Basic
import Linglib.Data.UD.Basic
import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Thematic Roles — type definitions

Neo-Davidsonian thematic roles as two-place predicates relating
entities to events. This file is the `Defs` partner to `LF.lean`: pure
type/structure declarations and the Fragment ↔ Theory bridge.

## Main definitions

* `ThematicRel` — `Entity → Event Time → Prop`, the core neo-Davidsonian
  relation type
* `EventRel` — event-first generalization (argument may be proposition,
  performance, content, etc.; cf. [rudin-2025b] §4.4–4.7)
* `ThematicFrame` — a model's assignment of role relations
  (agent / patient / theme / experiencer / goal / source /
  instrument / stimulus / holder)
* `ThetaRole.toRel` — Fragment-layer `ThetaRole` enum → `ThematicFrame` field

## References

* [davidson-1967], [parsons-1990] (neo-Davidsonian foundations)
* [rudin-2025b] (EventRel for non-entity arguments)
-/

namespace Semantics.ArgumentStructure

open Core.Time

/-- A thematic relation: a two-place predicate relating an entity to an event.
    The core neo-Davidsonian type.
    Agent(j, e) means "j is the agent of event e". -/
abbrev ThematicRel (Entity Time : Type*) [LinearOrder Time] :=
  Entity → Event Time → Prop

/-- A relation between an event and an argument of arbitrary sort.
    Generalizes `ThematicRel` past the entity-first restriction:
    arguments may be propositions, questions, performances, content
    individuals, or any other ontological category. The argument
    order is *event-first* (vs. ThematicRel's entity-first), reflecting
    the neo-Davidsonian convention for thematic roles vs. the more
    general event-relation pattern used by content/reenactment relations
    ([rudin-2025b], §4.4–4.7). -/
abbrev EventRel (Time α : Type*) [LinearOrder Time] := Event Time → α → Prop

/-- A thematic frame bundles thematic relations for a given model.

    Note: `holder` is a Theory-level role distinct from `agent` — it
    selects for states, not actions. The Fragment-layer `ThetaRole`
    enum does not include `holder` since `VendlerClass` already
    encodes dynamicity. -/
structure ThematicFrame (Entity Time : Type*) [LinearOrder Time] where
  /-- Agent: volitional causer -/
  agent : ThematicRel Entity Time
  /-- Patient: affected entity -/
  patient : ThematicRel Entity Time
  /-- Theme: entity in a state/location -/
  theme : ThematicRel Entity Time
  /-- Experiencer: perceiver/cognizer -/
  experiencer : ThematicRel Entity Time
  /-- Goal: recipient/target -/
  goal : ThematicRel Entity Time
  /-- Source: origin -/
  source : ThematicRel Entity Time
  /-- Instrument: means -/
  instrument : ThematicRel Entity Time
  /-- Stimulus: cause of experience -/
  stimulus : ThematicRel Entity Time
  /-- Holder: entity in a state. Distinct from Agent: selects for
      states, not actions. -/
  holder : ThematicRel Entity Time

/-- Map the Fragment-layer ThetaRole enum to the corresponding
    ThematicFrame field. Bridges lexical annotations to semantic content. -/
def ThetaRole.toRel {Entity Time : Type*} [LinearOrder Time]
    (θ : ThetaRole) (frame : ThematicFrame Entity Time) : ThematicRel Entity Time :=
  match θ with
  | .agent       => frame.agent
  | .patient     => frame.patient
  | .theme       => frame.theme
  | .experiencer => frame.experiencer
  | .goal        => frame.goal
  | .source      => frame.source
  | .instrument  => frame.instrument
  | .stimulus    => frame.stimulus

end Semantics.ArgumentStructure
