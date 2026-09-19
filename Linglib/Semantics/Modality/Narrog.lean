import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Narrog's semantic map of modality and mood

[narrog-2010] and [narrog-2012] locate the uses of modal markers in a two-dimensional semantic
space. *Volitivity* separates the modalities in which an element of will is present, deontic,
teleological, preferential, and boulomaic modality, from those in which it is absent, epistemic,
evidential, existential, and dynamic modality. *Speech act orientation* is the degree to which a
use is linked to the speech situation, that is to the speaker's own judgment at the time of
speech, to the hearer, or to the discourse. Its opposite pole is event orientation, a modal
judgment about conditions on the described event and its participants. Clausal mood and
illocutionary modification lie beyond modality proper at the speech act-oriented end. The
diachronic hypothesis stated on the map is that modal meanings change towards greater speech act
orientation, whatever the change does to volitivity.

## Main declarations

* `Modality.Narrog.Volitivity` is the horizontal dimension, a closed opposition.
* `Modality.Narrog.Orientation` is the vertical dimension at the three positions the book's
  figures label.
* `Modality.Narrog.Region` is a position on the map. Regions are preordered by orientation
  alone, so `s ≤ t` says that a change from `s` to `t` conforms to the directionality hypothesis,
  and two regions that differ only in volitivity lie below each other.

## Implementation notes

Both sources treat orientation as gradual and open-ended. [narrog-2012] derives it from
performativity, a form being used performatively to the extent that it qualifies a proposition
with respect to the current speech situation, and holds that no marker is event-oriented or
speech act-oriented out of context. `Orientation` keeps only the three labelled positions, of
which [narrog-2010] labels the two poles and calls the whole dimension speaker orientation. A
position therefore belongs to a use. Modal categories receive none here, since the book gives
deontic, boulomaic, epistemic, and evidential modality a broad range of orientations.

## TODO

`Modality.ModalFlavor` files teleological modality under the circumstantial flavor, but
teleological modality is volitive and circumstantial modality non-volitive, so a volitivity map
on flavors needs a finer flavor type.

## References

* [narrog-2010]
* [narrog-2012]
-/

namespace Modality.Narrog

/-- Volitivity is the presence or absence of an element of will in a modal meaning. -/
inductive Volitivity where
  /-- An element of will is present, as in obligation, permission, and wish. -/
  | volitive
  /-- No element of will is present, as in epistemic assessment, evidentiality, and ability. -/
  | nonVolitive
  deriving DecidableEq, Fintype, Repr

/-- Speech act orientation at the three positions labelled on the vertical axis of the map. -/
inductive Orientation where
  /-- The modal judgment concerns conditions on the described event and its participants. -/
  | eventOriented
  /-- The modal judgment is the speaker's own at the time of speech. -/
  | speakerOriented
  /-- The use is tied to the speech act itself, including the hearer and the discourse. Clausal
  mood and illocutionary modification lie here. -/
  | speechActOriented
  deriving DecidableEq, Fintype, Repr

namespace Orientation

/-- The positions are ordered as they are listed, from the event-oriented pole upwards. -/
instance : LinearOrder Orientation := LinearOrder.lift' Orientation.ctorIdx (by decide)

instance : BoundedOrder Orientation where
  top := speechActOriented
  le_top := by decide
  bot := eventOriented
  bot_le := by decide

theorem top_def : (⊤ : Orientation) = speechActOriented := rfl

theorem bot_def : (⊥ : Orientation) = eventOriented := rfl

end Orientation

/-- A region of the semantic map, the position of one use of a modal marker. -/
structure Region where
  volitivity : Volitivity
  orientation : Orientation
  deriving DecidableEq, Repr

namespace Region

/-- Regions are compared by orientation alone, so `s ≤ t` says that a change of meaning from `s`
to `t` does not decrease speech act orientation, which is the directionality hypothesis. -/
instance : Preorder Region := Preorder.lift orientation

variable {s t : Region} {v v' : Volitivity} {o o' : Orientation}

theorem le_def : s ≤ t ↔ s.orientation ≤ t.orientation := Iff.rfl

theorem lt_def : s < t ↔ s.orientation < t.orientation := Iff.rfl

instance : DecidableLE Region := fun _ _ ↦ decidable_of_iff _ le_def.symm

instance : DecidableLT Region := fun _ _ ↦ decidable_of_iff _ lt_def.symm

@[simp] theorem mk_le_mk : (⟨v, o⟩ : Region) ≤ ⟨v', o'⟩ ↔ o ≤ o' := Iff.rfl

@[simp] theorem mk_lt_mk : (⟨v, o⟩ : Region) < ⟨v', o'⟩ ↔ o < o' := Iff.rfl

/-- A change that keeps the orientation conforms whichever way it crosses the volitivity
dimension, so volitivity is independent of the direction of change. -/
theorem le_of_orientation_eq (h : s.orientation = t.orientation) : s ≤ t := h.le

/-- Every change into a speech act-oriented region conforms. -/
theorem le_of_orientation_eq_top (h : t.orientation = ⊤) (s : Region) : s ≤ t :=
  le_def.2 (h ▸ le_top)

/-- No change out of a speech act-oriented region into a lower one conforms. -/
theorem not_le_of_orientation_eq_top (hs : s.orientation = ⊤) (ht : t.orientation < ⊤) :
    ¬ s ≤ t := fun h ↦ (hs ▸ le_def.1 h).not_gt ht

/-- No change into an event-oriented region from a higher one conforms. -/
theorem not_le_of_orientation_eq_bot (hs : ⊥ < s.orientation) (ht : t.orientation = ⊥) :
    ¬ s ≤ t := fun h ↦ (ht ▸ le_def.1 h).not_gt hs

end Region

end Modality.Narrog
