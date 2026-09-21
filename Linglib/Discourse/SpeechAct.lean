module

public import Mathlib.Order.Max
public import Mathlib.Tactic.DeriveFintype

/-!
# Preparatory conditions of a request for information

A speech act is felicitous only if its preparatory conditions hold ([searle-1969]); for a
request, that the addressee is able to do what is requested. This file defines the preparatory
conditions of a request for information in the inventory of [francik-clark-1985], the obstacles
a speaker may see to getting the information: the addressee's ability to supply it, with knowing
it, remembering it, having noticed its source and being allowed to tell it as ways of being
able; the addressee's willingness; and the speaker's own memory of having asked already. The
conditions are partially ordered by specificity, a lower condition being a way of satisfying a
higher one, so that a request conditional on the lower presupposes the higher; the order has
neither a top nor a bottom, since willingness and the speaker's memory stand apart.

## Main definitions

* `Discourse.SpeechAct.PreparatoryCondition`, with its `PartialOrder`.

## References

* [searle-1969]
* [francik-clark-1985]
-/

@[expose] public section

namespace Discourse.SpeechAct

/-- A preparatory condition of a request for information, an obstacle to compliance. -/
inductive PreparatoryCondition where
  /-- The addressee is able to supply the information. -/
  | ability
  /-- The addressee knows the information. -/
  | knowledge
  /-- The addressee remembers the information. -/
  | memory
  /-- The addressee has noticed the source of the information. -/
  | source
  /-- The addressee is allowed to give the information. -/
  | permission
  /-- The addressee is willing to give the information. -/
  | willingness
  /-- The speaker has not already asked for the information. -/
  | speakerMemory
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace PreparatoryCondition

/-- Satisfying the first condition is a way of satisfying the second: knowing, remembering,
having noticed the source and being allowed to tell are ways of being able to supply the
information, and remembering or having noticed the source are ways of knowing it. -/
protected def le : PreparatoryCondition → PreparatoryCondition → Prop
  | .knowledge, .ability | .memory, .ability | .source, .ability | .permission, .ability
  | .memory, .knowledge | .source, .knowledge => True
  | c, d => c = d

instance : DecidableRel PreparatoryCondition.le := λ c d => by
  cases c <;> cases d <;> unfold PreparatoryCondition.le <;> infer_instance

instance : LE PreparatoryCondition := ⟨PreparatoryCondition.le⟩

instance : DecidableLE PreparatoryCondition :=
  inferInstanceAs (DecidableRel PreparatoryCondition.le)

instance : PartialOrder PreparatoryCondition where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : NoTopOrder PreparatoryCondition := ⟨by decide⟩

instance : NoBotOrder PreparatoryCondition := ⟨by decide⟩

end PreparatoryCondition

end Discourse.SpeechAct
