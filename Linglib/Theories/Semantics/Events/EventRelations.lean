import Linglib.Theories.Semantics.Events.Basic

/-!
# Event Relations (Generalized over Argument Sort)

A generalization of `ThematicRel` to arbitrary argument sorts. Where
`ThematicRel Entity Time := Entity → Ev Time → Prop` fixes the argument
sort to entities, `EventRel Time α := Ev Time → α → Prop` lets the
argument range over any type.

This is the type of relations like:

- `CONTENT : Ev Time → SemObj → Prop` — event-to-content relations
  where the argument is a propositional/question denotation, not an entity
- `REENACT : Ev Time → Performance Time → Prop` — event-to-performance
  relations, where the argument is itself an event
  (@cite{rudin-2025b}, §4.4–4.7)

`ThematicRel` is the special case `EventRel Time Entity` (with arguments
in the flipped order — entities first by Neo-Davidsonian convention). We
keep `ThematicRel` as its own abbrev because the entity-first projection
is the dominant pattern in lexical entries.
-/

namespace Semantics.Events

open Core.Time

/-- A relation between an event and an argument of arbitrary sort.

    Generalizes `ThematicRel` past the entity-first restriction:
    arguments may be propositions, questions, performances, content
    individuals, or any other ontological category that the analysis
    requires. -/
abbrev EventRel (Time α : Type*) [LE Time] := Ev Time → α → Prop

end Semantics.Events
