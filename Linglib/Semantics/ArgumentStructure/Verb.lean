import Linglib.Syntax.Category.Verb.Basic
import Linglib.Semantics.ArgumentStructure.ThematicRole
import Linglib.Semantics.ArgumentStructure.ThetaRole
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.ArgumentStructure.ChangeOfState

/-!
# The denotation of a verb

This file defines the theta roles of a verb's subject and object, read off their entailment
profiles, and the event predicate that a change-of-state verb denotes. Following Beavers and
Koontz-Garboden, the root of such a verb denotes a state predicate, and the verbal heads of a
`ChangeOfStateModel` build the event predicate from it: the inchoative is the change-of-state
head over the root's state, and the causative is the causative head over the inchoative. Which
of them a verb denotes is chosen by the kind signature of its root (`Verb.Model.denote`).

## Main definitions

* `Verb.subjectRole`, `Verb.objectRole`: the theta roles of the subject and the object.
* `Verb.Model`: a change-of-state model with an interpretation of the verbs' roots.
* `Verb.Model.inchoative`, `Verb.Model.causative`, `Verb.Model.denote`: the denotations.

## Main results

* `Verb.Model.exists_inchoative_of_causative`: the causative entails the inchoative.
* `Verb.Model.exists_rootState_of_denote`: a verb whose root has a result entails the result
  state.

## References

* [beavers-koontz-garboden-2020]
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

/-! ### The denotation of a change-of-state verb -/

/-- A model in which verbs are interpreted is a change-of-state model together with the state
predicate that each verb's root denotes and the manner predicate of a root without a change. A
verb stands in for its root, which most entries leave anonymous. -/
structure Verb.Model (Entity State Event : Type*) extends
    ChangeOfStateModel Entity State Event where
  /-- A state of the property of the verb's root holds of the individual. -/
  rootState : Verb → Entity → State → Prop
  /-- The manner that the verb's root specifies holds of the event. -/
  manner : Verb → Event → Prop

namespace Verb.Model

variable {Entity State Event : Type*} (M : Verb.Model Entity State Event) {v : Verb}
  {x y : Entity} {e : Event}

/-- The inchoative denotation of the verb is the change-of-state head over the state predicate
of its root. -/
def inchoative (v : Verb) : Entity → Event → Prop := M.vBecome (M.rootState v)

/-- The causative denotation of the verb is the causative head over its inchoative. -/
def causative (v : Verb) (y x : Entity) : Event → Prop := M.vCause (M.inchoative v x) y

/-- The denotation of the verb is chosen by the closed kind signature of its root. It is the
causative for a root with a cause, the inchoative for another root with a result, and the manner
otherwise. -/
def denote (v : Verb) (y x : Entity) : Event → Prop :=
  if Root.Kind.cause ∈ v.root.closedKinds then M.causative v y x
  else if Root.Kind.result ∈ v.root.closedKinds then M.inchoative v x
  else M.manner v

variable {M}

/-- The causative entails the inchoative. -/
theorem exists_inchoative_of_causative (h : M.causative v y x e) : ∃ e', M.inchoative v x e' :=
  ChangeOfStateModel.exists_of_vCause h

/-- The causative entails that a change gives rise to a state of the root's property. -/
theorem exists_rootState_of_causative (h : M.causative v y x e) :
    ∃ e' s, M.become s e' ∧ M.rootState v x s :=
  exists_inchoative_of_causative h

/-- The denotation of a verb whose root has a result entails that a change gives rise to a
state of the root's property. -/
theorem exists_rootState_of_denote (hres : Root.Kind.result ∈ v.root.closedKinds)
    (h : M.denote v y x e) : ∃ e' s, M.become s e' ∧ M.rootState v x s := by
  unfold denote at h
  split_ifs at h
  · exact exists_rootState_of_causative h
  · exact ⟨e, h⟩

/-- The denotation of a verb whose template embeds a result state entails that a change gives
rise to a state of the root's property. -/
theorem exists_rootState_of_denote_of_hasResultState (ht : v.root.template.HasResultState)
    (h : M.denote v y x e) : ∃ e' s, M.become s e' ∧ M.rootState v x s :=
  exists_rootState_of_denote ((Semantics.Root.template_hasResultState_iff v.root).mp ht) h

end Verb.Model
