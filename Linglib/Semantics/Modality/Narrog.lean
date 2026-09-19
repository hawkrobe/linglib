import Linglib.Semantics.Modality.Basic

/-!
# Volitivity and speech act orientation

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

* `Modality.ModalFlavor.IsVolitive` is the horizontal dimension, a closed opposition.
* `Modality.SpeechActOrientation` is the vertical dimension at the three positions the book's
  figures label, ordered upwards. A change of use from `o` to `o'` conforms to the directionality
  hypothesis when `o ≤ o'`; since the hypothesis is silent on volitivity, no type pairs the two
  dimensions.

## Implementation notes

Both sources treat orientation as gradual and open-ended. [narrog-2012] derives it from
performativity, a form being used performatively to the extent that it qualifies a proposition
with respect to the current speech situation, and holds that no marker is event-oriented or
speech act-oriented out of context. `SpeechActOrientation` keeps only the three labelled
positions, of which [narrog-2010] labels the two poles and calls the whole dimension speaker
orientation. A position therefore belongs to a use. Modal categories receive none here, since
the book gives deontic, boulomaic, epistemic, and evidential modality a broad range of
orientations.

`ModalFlavor` files teleological modality under the circumstantial flavor, which `IsVolitive`
treats as non-volitive, while the book places teleological modality on the volitive side, next
to a border with circumstantial modality that it calls fluid.

## References

* [narrog-2010]
* [narrog-2012]
-/

namespace Modality

/-- A flavor is volitive when an element of will is present in it, as in obligation,
permission, and wish, and non-volitive otherwise, as in epistemic assessment and ability. -/
def ModalFlavor.IsVolitive (f : ModalFlavor) : Prop := f = .deontic ∨ f = .bouletic

instance : DecidablePred ModalFlavor.IsVolitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Speech act orientation at the three positions labelled on the vertical axis of the map. -/
inductive SpeechActOrientation where
  /-- The modal judgment concerns conditions on the described event and its participants. -/
  | eventOriented
  /-- The modal judgment is the speaker's own at the time of speech. -/
  | speakerOriented
  /-- The use is tied to the speech act itself, including the hearer and the discourse. Clausal
  mood and illocutionary modification lie here. -/
  | speechActOriented
  deriving DecidableEq, Fintype, Repr

namespace SpeechActOrientation

/-- The positions are ordered as they are listed, from the event-oriented pole upwards. -/
instance : LinearOrder SpeechActOrientation :=
  LinearOrder.lift' SpeechActOrientation.ctorIdx (by decide)

instance : BoundedOrder SpeechActOrientation where
  top := speechActOriented
  le_top := by decide
  bot := eventOriented
  bot_le := by decide

theorem top_def : (⊤ : SpeechActOrientation) = speechActOriented := rfl

theorem bot_def : (⊥ : SpeechActOrientation) = eventOriented := rfl

end SpeechActOrientation

end Modality
