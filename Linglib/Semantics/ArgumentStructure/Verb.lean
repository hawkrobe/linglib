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
head over the root's state, and the causative is the causative head over the inchoative. The
kinds of entailment that a root carries are meaning postulates on its state predicate, and a
model respects a root when they hold (`Verb.Model.Respects`). Which template a verb occurs in is
not read off its root.

## Main definitions

* `Verb.subjectRole`, `Verb.objectRole`: the theta roles of the subject and the object.
* `Verb.Model`: a change-of-state model with an interpretation of the verbs' roots.
* `Verb.Model.inchoative`, `Verb.Model.causative`: the denotations of the two templates.
* `Verb.Model.Entails`, `Verb.Model.Respects`: the meaning postulates of a root's kinds.

## Main results

* `Verb.Model.exists_inchoative_of_causative`: the causative entails the inchoative.
* `Verb.Model.Entails.anti`: the postulates are downward closed along the order on kinds, so
  the collocational closure of a signature is sound.

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

/-- The root of `v` entails change when every state of its property arises from a change. -/
def EntailsChange (v : Verb) : Prop := ∀ x s, M.rootState v x s → ∃ e, M.become s e

/-- The root of `v` entails a cause when every state of its property arises from a change that
some event causes. -/
def EntailsCause (v : Verb) : Prop :=
  ∀ x s, M.rootState v x s → ∃ e w, M.become s e ∧ M.cause w e

/-- The meaning postulate of a kind of root entailment. A result is a change giving rise to the
root's state and a cause is a cause of that change, while a state and a manner impose nothing
beyond the root's own predicate. -/
def Entails (v : Verb) : Root.Kind → Prop
  | .result => M.EntailsChange v
  | .cause => M.EntailsCause v
  | .state | .manner => True

/-- The model respects the root of `v` when the postulate of each of the root's kinds holds. -/
def Respects (v : Verb) : Prop := ∀ k ∈ v.root.kinds, M.Entails v k

variable {M}

/-- The causative entails the inchoative. -/
theorem exists_inchoative_of_causative (h : M.causative v y x e) : ∃ e', M.inchoative v x e' :=
  ChangeOfStateModel.exists_of_vCause h

/-- The causative entails that a change gives rise to a state of the root's property. -/
theorem exists_rootState_of_causative (h : M.causative v y x e) :
    ∃ e' s, M.become s e' ∧ M.rootState v x s :=
  exists_inchoative_of_causative h

theorem EntailsCause.entailsChange (h : M.EntailsCause v) : M.EntailsChange v :=
  fun x s hs ↦ let ⟨e, _, hb, _⟩ := h x s hs; ⟨e, hb⟩

/-- The postulates are downward closed along the collocational order on kinds, since a cause
entails a change and both entail a state. -/
theorem Entails.anti {j k : Root.Kind} (hkj : k ≤ j) (h : M.Entails v j) : M.Entails v k := by
  cases hkj with
  | refl => exact h
  | state_result | state_cause => trivial
  | result_cause => exact EntailsCause.entailsChange h

/-- Every model respects a root that carries only a state or a manner. -/
theorem respects_of_kinds_subset (h : v.root.kinds ⊆ {.state, .manner}) : M.Respects v :=
  fun k hk ↦ by
    rcases Finset.mem_insert.1 (h hk) with rfl | hm
    · trivial
    · rw [Finset.mem_singleton.1 hm]; trivial

/-- A model that respects a root satisfies the postulate of every kind in the collocational
closure of its signature. -/
theorem Respects.entails_of_mem_closedKinds (h : M.Respects v) {k : Root.Kind}
    (hk : k ∈ v.root.closedKinds) : M.Entails v k :=
  let ⟨j, hj, hkj⟩ := Root.Kinds.mem_close.1 hk
  (h j hj).anti hkj

end Verb.Model
