import Linglib.Semantics.Root.Kinds

/-!
# Change-of-state models

This file defines the models in which the event-structural decomposition of change-of-state
verbs is interpreted. A model gives the three relations that the verbal heads introduce: an
eventuality gives rise to a state, an eventuality causes another, and an individual is the
effector of an eventuality. The heads themselves are operators on predicates. `vBecome` turns a
state predicate into the predicate of the events that give rise to such a state, and `vCause`
turns an event predicate into the predicate of the events that cause such an event. The
eventualities are an arbitrary type, so they may be events with run times, states, or both.

A state predicate may itself entail a change, a cause of the change, or a manner of the causing
event. These are the meaning postulates that Beavers and Koontz-Garboden attach to the state
predicate of a root, one for each kind of entailment, and a model respects a kind signature for
a predicate when the postulates of its kinds hold.

## Main definitions

* `ArgumentStructure.ChangeOfStateModel`: the relations `become`, `cause` and `effector`.
* `ChangeOfStateModel.vBecome`, `ChangeOfStateModel.vCause`: the two heads.
* `ChangeOfStateModel.EntailsChange`, `EntailsCause`, `EntailsManner`: the postulates on a state
  predicate.
* `ChangeOfStateModel.Respects`: the postulates of every kind in a signature hold.

## Main results

* `ChangeOfStateModel.Entails.anti`: the postulates are downward closed along the order on kinds.
* `ChangeOfStateModel.respects_close`: a signature and its collocational closure are respected
  together.

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

/-! ### Meaning postulates on a state predicate -/

section Postulates

open Semantics

variable (M) (P : Entity → State → Prop) (Q : Event → Prop) {ks : Root.Kinds}

/-- The state predicate `P` entails change when every state of which it holds arises from a
change. -/
def EntailsChange : Prop := ∀ x s, P x s → ∃ e, M.become s e

/-- The state predicate `P` entails a cause when every state of which it holds arises from a
change that some event causes. -/
def EntailsCause : Prop := ∀ x s, P x s → ∃ e v, M.become s e ∧ M.cause v e

/-- The state predicate `P` entails the manner `Q` when every state of which it holds arises
from a change whose every cause is a `Q`-event. -/
def EntailsManner : Prop := ∀ x s, P x s → ∃ e, M.become s e ∧ ∀ v, M.cause v e → Q v

/-- The meaning postulate of a kind of root entailment for the state predicate `P`, with `Q` the
manner. A state imposes nothing beyond the predicate itself. -/
def Entails : Root.Kind → Prop
  | .state => True
  | .result => M.EntailsChange P
  | .cause => M.EntailsCause P
  | .manner => M.EntailsManner P Q

/-- The model respects the kind signature `ks` for `P` and `Q` when the postulate of each of its
kinds holds. -/
def Respects (ks : Root.Kinds) : Prop := ∀ k ∈ ks, M.Entails P Q k

variable {M P Q}

theorem EntailsCause.entailsChange (h : M.EntailsCause P) : M.EntailsChange P :=
  fun x s hs ↦ let ⟨e, _, hb, _⟩ := h x s hs; ⟨e, hb⟩

theorem EntailsManner.entailsChange (h : M.EntailsManner P Q) : M.EntailsChange P :=
  fun x s hs ↦ let ⟨e, hb, _⟩ := h x s hs; ⟨e, hb⟩

/-- The postulates are downward closed along the collocational order on kinds, since a cause
entails a change and both entail a state. -/
theorem Entails.anti {j k : Root.Kind} (hkj : k ≤ j) (h : M.Entails P Q j) :
    M.Entails P Q k := by
  cases hkj with
  | refl => exact h
  | state_result | state_cause => trivial
  | result_cause => exact EntailsCause.entailsChange h

theorem Respects.mono {ks' : Root.Kinds} (hks : ks ⊆ ks') (h : M.Respects P Q ks') :
    M.Respects P Q ks :=
  fun k hk ↦ h k (hks hk)

/-- A signature is respected iff its collocational closure is. -/
@[simp] theorem respects_close : M.Respects P Q ks.close ↔ M.Respects P Q ks :=
  ⟨Respects.mono (Root.Kinds.subset_close ks), fun h _ hk ↦
    let ⟨j, hj, hkj⟩ := Root.Kinds.mem_close.1 hk
    (h j hj).anti hkj⟩

/-- A model that respects a signature whose closure has a result satisfies the postulate of
change. -/
theorem Respects.entailsChange (h : M.Respects P Q ks) (hr : Root.Kind.result ∈ ks.close) :
    M.EntailsChange P :=
  respects_close.2 h _ hr

end Postulates

end ChangeOfStateModel

end ArgumentStructure
