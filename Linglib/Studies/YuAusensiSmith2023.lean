import Linglib.Studies.BeaversEtAl2021
import Linglib.Data.Examples.YuAusensiSmith2023

/-!
# Yu, Ausensi & Smith (2023): States and Changes-of-State in the Semantics of Result Roots

This file formalizes the account of result roots by Yu, Ausensi and Smith. The roots of result
verbs are of two types. A property concept root, such as that of *open*, relates an individual
to a state. A change-of-state root, such as that of *break*, relates an individual to an event
of change into the state the root names, so it is the change-of-state head applied to a state
predicate (`changeOfState`). Events and states are sorts of one domain of eventualities.

Three predictions follow from the types. *Again* attached to a change-of-state root presupposes
an earlier change, so such verbs have no restitutive reading, a prediction shared with Beavers
and Koontz-Garboden's stative roots that entail change. A durative *for*-phrase measures a state
only where a constituent holds of states, which a change-of-state root never does
(`not_isState_of_changeOfState`). And a root modifies a resultative verb phrase, by conjunction
with it, only if it holds of events, so a property concept root cannot
(`not_modifies_of_isStative`) while a change-of-state root can, with the holder of its state
existentially closed.

## Implementation notes

* The causative head relates an event to the state it causes, as in the paper, with no
  change-of-state head beneath it and the agent introduced separately.
* The derivations with Voice and existential closure at the verb phrase are not represented.

## References

* [yu-ausensi-smith-2023]
* [beavers-koontz-garboden-2020]
-/

namespace YuAusensiSmith2023

open ArgumentStructure.EventStructure Presupposition

/-! ### Roots of two types -/

section Roots

variable {Entity Ev : Type*} (M : Interpretation Entity Ev Ev) (IsState : Ev → Prop)
  {B : Entity → Ev → Prop} {L : Ev → Prop} {x : Entity} {e : Ev}

/-- The interpretation is sorted when a change is an event giving rise to a state, and a cause
is an event bringing about a state. -/
structure Sorted : Prop where
  isState_of_become {s e : Ev} : M.become s e → IsState s
  not_isState_of_become {s e : Ev} : M.become s e → ¬ IsState e
  isState_of_cause {e s : Ev} : M.cause e s → IsState s
  not_isState_of_cause {e s : Ev} : M.cause e s → ¬ IsState e

/-- A property concept root holds of states only. -/
def IsStative (B : Entity → Ev → Prop) : Prop := ∀ x s, B x s → IsState s

/-- A change-of-state root relates an individual to an event of change into a state of `B`. -/
def changeOfState (B : Entity → Ev → Prop) : Entity → Ev → Prop := M.vBecome B

/-- The causative head relates an event to a state of `L` that it causes. -/
def vCause (L : Ev → Prop) (e : Ev) : Prop := ∃ s, M.cause e s ∧ L s

/-- A root modifies a verb phrase by conjunction with it. -/
def modify (R : Entity → Ev → Prop) (V : Ev → Prop) (x : Entity) (e : Ev) : Prop := R x e ∧ V e

variable {M IsState}

/-- A change-of-state root holds of no state, so no constituent built on it alone is stative. -/
theorem not_isState_of_changeOfState (h : Sorted M IsState) (he : changeOfState M B x e) :
    ¬ IsState e :=
  let ⟨_, hb, _⟩ := he; h.not_isState_of_become hb

/-- A causative verb phrase holds of no state. -/
theorem not_isState_of_vCause (h : Sorted M IsState) (he : vCause M L e) : ¬ IsState e :=
  let ⟨_, hc, _⟩ := he; h.not_isState_of_cause hc

/-- A property concept root cannot modify a causative verb phrase, since nothing is both a
state and an event. -/
theorem not_modifies_of_isStative (h : Sorted M IsState) (hB : IsStative IsState B) :
    ¬ modify B (vCause M L) x e :=
  fun ⟨hs, hv⟩ ↦ not_isState_of_vCause h hv (hB x e hs)

/-- A resultative built on a change-of-state root entails that something came to be in a state
of the root and that the event caused a state of the result phrase. -/
theorem exists_of_modify_changeOfState (h : ∃ x, modify (changeOfState M B) (vCause M L) x e) :
    (∃ x s, M.become s e ∧ B x s) ∧ ∃ s, M.cause e s ∧ L s :=
  let ⟨x, ⟨s, hb, hs⟩, hv⟩ := h; ⟨⟨x, s, hb, hs⟩, hv⟩

end Roots

/-! ### *Again* -/

section Again

variable {Entity State Event : Type*} {M : Interpretation Entity State Event}
  {lt : Event → Event → Prop} {B : Entity → State → Prop} {x : Entity} {e : Event}

/-- *Again* attached to a change-of-state root presupposes an earlier change, so no attachment
gives a restitutive reading. -/
theorem change_of_again_changeOfState (h : (again lt (M.vBecome B x)).presup e) :
    ∃ e', lt e' e ∧ ∃ s, M.become s e' :=
  BeaversEtAl2021.change_of_againRepetitiveBecome_presup M h

end Again

/-! ### Breaking the corpse loose -/

/-- The eventualities of *a couple of monks broke the corpse loose from the deck*. -/
inductive Ev
  | breaking
  | broken
  | loose
  deriving DecidableEq

/-- The breaking gives rise to the broken state and causes the loose one. -/
def monks : Interpretation Unit Ev Ev where
  become s e := s = .broken ∧ e = .breaking
  cause e s := e = .breaking ∧ s = .loose
  effector _ e := e = .breaking

/-- The states of the scene. -/
def IsState (v : Ev) : Prop := v ≠ .breaking

instance : DecidablePred IsState := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

theorem sorted_monks : Sorted monks IsState where
  isState_of_become h := by rw [h.1]; decide
  not_isState_of_become h := by rw [h.2]; decide
  isState_of_cause h := by rw [h.2]; decide
  not_isState_of_cause h := by rw [h.1]; decide

/-- The change-of-state root modifies the resultative verb phrase, with the broken state and
the loose state distinct. -/
theorem modify_monks :
    modify (changeOfState monks fun _ s ↦ s = .broken) (vCause monks (· = .loose)) ()
      .breaking :=
  ⟨⟨.broken, ⟨rfl, rfl⟩, rfl⟩, .loose, ⟨rfl, rfl⟩, rfl⟩

/-- On the stative analysis of the root the result phrase must describe the root's own state,
and no state of the scene is both the broken one and the loose one. -/
theorem not_stative_modify_monks : ¬ ∃ s, modify (fun _ s ↦ s = Ev.broken) (· = .loose) () s :=
  fun ⟨_, hb, hl⟩ ↦ Ev.noConfusion (hb.symm.trans hl)

/-! ### The judgments -/

open Data.Examples in
/-- *Again* has a restitutive reading in the examples exactly with a property concept root. -/
theorem restitutive_iff_propertyConcept :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" = some "again" →
      (e.readings.lookup "restitutive" = some .acceptable ↔
        e.feature? "root class" = some "property concept") := by
  decide

open Data.Examples in
/-- A *for*-phrase has an internal reading in the examples exactly with a property concept
root. -/
theorem internal_iff_propertyConcept :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" = some "for-phrase" →
      (e.readings.lookup "internal" = some .acceptable ↔
        e.feature? "root class" = some "property concept") := by
  decide

open Data.Examples in
/-- A root modifies a resultative in the examples exactly when it is a change-of-state root. -/
theorem modifier_iff_changeOfState :
    ∀ e ∈ Examples.all, e.feature? "diagnostic" = some "resultative modifier" →
      (e.judgment = .acceptable ↔ e.feature? "root class" = some "change of state") := by
  decide

end YuAusensiSmith2023
