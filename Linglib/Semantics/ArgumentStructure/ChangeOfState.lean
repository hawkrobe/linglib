import Mathlib.Order.Basic

/-!
# Change-of-state models

This file defines the models in which the event-structural decomposition of change-of-state
verbs is interpreted. A model gives the three relations that the verbal heads introduce: an
eventuality gives rise to a state, an eventuality causes another, and an individual is the
effector of an eventuality. The heads themselves are operators on predicates. `vBecome` turns a
state predicate into the predicate of the events that give rise to such a state, and `vCause`
turns an event predicate into the predicate of the events that cause such an event. The
eventualities are an arbitrary type, so they may be events with run times, states, or both.

## Main definitions

* `ArgumentStructure.ChangeOfStateModel`: the relations `become`, `cause` and `effector`.
* `ArgumentStructure.ChangeOfStateModel.vBecome`: the head introducing a change.
* `ArgumentStructure.ChangeOfStateModel.vCause`: the head introducing a causing event and its
  effector.

## References

* [beavers-koontz-garboden-2020]
-/

namespace ArgumentStructure

/-- A model of the relations that the change-of-state heads introduce. -/
structure ChangeOfStateModel (Entity State Event : Type*) where
  /-- The eventuality gives rise to the state. -/
  become : State → Event → Prop
  /-- The first eventuality causes the second. -/
  cause : Event → Event → Prop
  /-- The individual is the effector of the eventuality. -/
  effector : Entity → Event → Prop

namespace ChangeOfStateModel

variable {Entity State Event : Type*} (M : ChangeOfStateModel Entity State Event)
  {P P' : Entity → State → Prop} {Q Q' : Event → Prop} {x y : Entity} {e : Event}

/-- The change-of-state head `vBecome P x` holds of the events that give rise to a state of
which `P x` holds. -/
def vBecome (P : Entity → State → Prop) (x : Entity) (e : Event) : Prop :=
  ∃ s, M.become s e ∧ P x s

/-- The causative head `vCause Q y` holds of the events whose effector is `y` and which cause
an event of which `Q` holds. -/
def vCause (Q : Event → Prop) (y : Entity) (v : Event) : Prop :=
  ∃ e, M.effector y v ∧ M.cause v e ∧ Q e

variable {M}

theorem vBecome_mono (h : P ≤ P') : M.vBecome P ≤ M.vBecome P' :=
  fun x _ ⟨s, hb, hP⟩ ↦ ⟨s, hb, h x s hP⟩

theorem vCause_mono (h : Q ≤ Q') : M.vCause Q ≤ M.vCause Q' :=
  fun _ _ ⟨e, he, hc, hQ⟩ ↦ ⟨e, he, hc, h e hQ⟩

/-- A change gives rise to a state of the predicate. -/
theorem exists_state_of_vBecome (h : M.vBecome P x e) : ∃ s, M.become s e ∧ P x s := h

/-- A causing event has a caused event of the embedded predicate. -/
theorem exists_of_vCause (h : M.vCause Q y e) : ∃ e', Q e' :=
  let ⟨e', _, _, hQ⟩ := h; ⟨e', hQ⟩

end ChangeOfStateModel

end ArgumentStructure
