import Linglib.Syntax.Category.Verb.Basic
import Linglib.Semantics.ArgumentStructure.ThematicRole
import Linglib.Semantics.ArgumentStructure.ThetaRole
import Linglib.Semantics.ArgumentStructure.EventStructure

/-!
# The theta roles of a verb

This file reads the theta roles of a verb's subject and object off their entailment profiles,
and defines when a verb is unaccusative.

## Main definitions

* `Verb.IsUnaccusative`: the verb's sole argument is its underlying object.
* `Verb.subjectRole`, `Verb.objectRole`: the theta roles of the subject and the object.

## References

* [dowty-1991]
* [kratzer-1996]
-/

open ArgumentStructure
open Semantics

/-! ### The theta-grid (derived from the proto-role profiles) -/

/-- The verb is unaccusative when its voice, if recorded, introduces no external argument
([kratzer-1996]), and otherwise when some frame of its has none (`ArgumentFrame.IsUnaccusative`),
its sole argument the underlying object. -/
def Verb.IsUnaccusative (v : Verb) : Prop :=
  match v.voiceType with
  | some vt => ¬ vt.AssignsTheta
  | none => ∃ fr ∈ v.frames, fr.IsUnaccusative

instance : DecidablePred Verb.IsUnaccusative := fun v ↦ by
  unfold Verb.IsUnaccusative; split <;> infer_instance

/-- The subject's theta-role, from its entailment profile (`EntailmentProfile.toRole`). -/
def Verb.subjectRole (v : Verb) : Option ThetaRole :=
  v.subjectProfile?.bind (·.toRole)

/-- The object's theta-role, from its entailment profile. -/
def Verb.objectRole (v : Verb) : Option ThetaRole :=
  v.objectProfile?.bind (·.toRole)
