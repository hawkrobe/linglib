module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Unaccusativity

This file defines when a verb entry is unaccusative. An intransitive verb is unaccusative when
its sole argument is an underlying object and no external argument is introduced, as with
*arrive* and *melt*, and unergative otherwise, as with *work*. The classification is read off
the entry's voice where one is recorded, and otherwise off its frames.

## Main definitions

* `Verb.IsUnaccusative`: the verb's voice introduces no external argument, or some frame of
  the verb has none.

## References

* [kratzer-1996]
-/

@[expose] public section

/-- The verb is unaccusative when its voice, if recorded, introduces no external argument, and
otherwise when some frame of its has none, its sole argument being the underlying object. -/
def Verb.IsUnaccusative (v : Verb) : Prop :=
  match v.voiceType with
  | some vt => ¬ vt.AssignsTheta
  | none => ∃ fr ∈ v.frames, fr.IsUnaccusative

instance : DecidablePred Verb.IsUnaccusative := fun v ↦ by
  unfold Verb.IsUnaccusative; split <;> infer_instance
