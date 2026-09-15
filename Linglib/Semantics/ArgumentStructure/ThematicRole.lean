import Linglib.Semantics.Events.Basic

/-!
# Thematic roles

This file defines neo-Davidsonian thematic relations ([davidson-1967], [parsons-1990]). A
thematic relation relates an entity to an event, an event relation generalizes the second
argument to any sort ([rudin-2025b]), and a thematic frame assigns the standard role relations
of a model.

## Main definitions

* `ThematicRel` — a relation between entities and events.
* `EventRel` — a relation between events and arguments of any sort, event first.
* `ThematicFrame` — a model's assignment of the role relations.

## References

* [davidson-1967], [parsons-1990], [rudin-2025b]
-/

namespace ArgumentStructure

/-- A thematic relation relates an entity to an event: `agent j e` says that `j` is the agent
of `e`. -/
abbrev ThematicRel (Entity T : Type*) [LinearOrder T] := Entity → Event T → Prop

/-- A relation between an event and an argument of any sort, such as a proposition, a question
or a performance ([rudin-2025b]); the event comes first, as for content and reenactment
relations, where `ThematicRel` puts the entity first. -/
abbrev EventRel (T α : Type*) [LinearOrder T] := Event T → α → Prop

/-- A thematic frame assigns the role relations of a model. The holder role is distinct from
the agent: it selects states, where the agent selects actions. -/
structure ThematicFrame (Entity T : Type*) [LinearOrder T] where
  /-- The agent, the volitional causer. -/
  agent : ThematicRel Entity T
  /-- The patient, the affected entity. -/
  patient : ThematicRel Entity T
  /-- The theme, the entity in a state or location. -/
  theme : ThematicRel Entity T
  /-- The experiencer, the perceiver or cognizer. -/
  experiencer : ThematicRel Entity T
  /-- The goal, the recipient or target. -/
  goal : ThematicRel Entity T
  /-- The source, the origin. -/
  source : ThematicRel Entity T
  /-- The instrument, the means. -/
  instrument : ThematicRel Entity T
  /-- The stimulus, the cause of an experience. -/
  stimulus : ThematicRel Entity T
  /-- The holder, the entity in a state. -/
  holder : ThematicRel Entity T

end ArgumentStructure
