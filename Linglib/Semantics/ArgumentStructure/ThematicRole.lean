module

public import Mathlib.Tactic.TypeStar

/-!
# Thematic roles

This file defines the thematic relations of neo-Davidsonian semantics, after Davidson and
Parsons. A thematic relation relates an entity to an event of an event domain `E`; Rudin's event
relations relate an event to an argument of any sort, such as a proposition or a performance.

## Main definitions

* `ThematicRel`: a relation between entities and events.
* `EventRel`: a relation between events and arguments of any sort, event first.
* `ThematicFrame`: a model's assignment of the standard role relations.

## References

* [davidson-1967]
* [parsons-1990]
* [rudin-2025b]
-/

@[expose] public section

namespace ArgumentStructure

/-- A thematic relation relates an entity to an event: `agent j e` says that `j` is the agent
of `e`. -/
abbrev ThematicRel (Entity E : Type*) := Entity → E → Prop

/-- A relation between an event and an argument of any sort, such as a proposition, a question
or a performance ([rudin-2025b]); the event comes first, as for content and reenactment
relations, where `ThematicRel` puts the entity first. -/
abbrev EventRel (E α : Type*) := E → α → Prop

/-- A thematic frame assigns the role relations of a model. The holder role is distinct from
the agent: it selects states, where the agent selects actions. -/
structure ThematicFrame (Entity E : Type*) where
  /-- The agent, the volitional causer. -/
  agent : ThematicRel Entity E
  /-- The patient, the affected entity. -/
  patient : ThematicRel Entity E
  /-- The theme, the entity in a state or location. -/
  theme : ThematicRel Entity E
  /-- The experiencer, the perceiver or cognizer. -/
  experiencer : ThematicRel Entity E
  /-- The goal, the recipient or target. -/
  goal : ThematicRel Entity E
  /-- The source, the origin. -/
  source : ThematicRel Entity E
  /-- The instrument, the means. -/
  instrument : ThematicRel Entity E
  /-- The stimulus, the cause of an experience. -/
  stimulus : ThematicRel Entity E
  /-- The holder, the entity in a state. -/
  holder : ThematicRel Entity E

end ArgumentStructure
