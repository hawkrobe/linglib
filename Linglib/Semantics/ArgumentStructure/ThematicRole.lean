module

public import Mathlib.Tactic.TypeStar

/-!
# Thematic roles

This file defines the thematic relations of neo-Davidsonian semantics, after Davidson and
Parsons. A thematic relation relates an entity to an event of an event domain `E`.

## Main definitions

* `ThematicFrame`: a model's assignment of the standard role relations.

## References

* [davidson-1967]
* [parsons-1990]
-/

@[expose] public section

namespace ArgumentStructure

/-- A thematic frame assigns the role relations of a model, each relating an entity to an event,
so that `agent j e` says that `j` is the agent of `e`. The holder role is distinct from the
agent: it selects states, where the agent selects actions. -/
structure ThematicFrame (Entity E : Type*) where
  /-- The agent, the volitional causer. -/
  agent : Entity → E → Prop
  /-- The patient, the affected entity. -/
  patient : Entity → E → Prop
  /-- The theme, the entity in a state or location. -/
  theme : Entity → E → Prop
  /-- The experiencer, the perceiver or cognizer. -/
  experiencer : Entity → E → Prop
  /-- The goal, the recipient or target. -/
  goal : Entity → E → Prop
  /-- The source, the origin. -/
  source : Entity → E → Prop
  /-- The instrument, the means. -/
  instrument : Entity → E → Prop
  /-- The stimulus, the cause of an experience. -/
  stimulus : Entity → E → Prop
  /-- The holder, the entity in a state. -/
  holder : Entity → E → Prop

end ArgumentStructure
