module

public import Linglib.Semantics.Modality.Kratzer.ConversationalBackground
public import Linglib.Semantics.Mood.SpeechEvent

/-!
# Modal anchors

This file defines the sources from which an event projects a modal domain — the content
of a speech act, the content of an attitude, or the decision that caused a volitional
event — the partial anchoring function a source assignment induces, and the definedness
conditions a modal item may impose on its anchor.

## Main definitions

* `ModalSource` — what an event projects from, with its `background` and `flavor`.
* `anchoring` — the anchoring function of a source assignment, defined on events with a
  source.
* `AnchorConstraint` — the definedness condition an item imposes, and `Admits`.

## References

* [hacquard-2006]
* [hacquard-2010]
* [alonso-ovalle-menendez-benito-2018]
* [alonso-ovalle-royer-2024]
-/

@[expose] public section

namespace Modality

open Mood Modality

variable {Event W : Type*}

/-- An event projects a modal domain from a speech act's content `CON(e*)`, from an attitude
holder's doxastic alternatives, or from the fulfilment conditions of the decision that caused a
volitional event. -/
inductive ModalSource (W : Type*)
  | speechAct (sa : SpeechEvent W)
  | attitude (dox : ConvBackground W)
  | decision (fulfilled : ConvBackground W)

/-- The conversational background a source projects. -/
def ModalSource.background : ModalSource W → ConvBackground W
  | .speechAct sa => sa.content
  | .attitude dox => dox
  | .decision fulfilled => fulfilled

/-- The flavor a source projects is the speech act's own, epistemic for an attitude, and
circumstantial, as random choice, for a decision. -/
def ModalSource.flavor : ModalSource W → ModalFlavor
  | .speechAct sa => sa.force.primaryFlavor
  | .attitude _ => .epistemic
  | .decision _ => .circumstantial

/-- A source is a decision. -/
def ModalSource.IsDecision : ModalSource W → Prop
  | .decision _ => True
  | _ => False

instance (s : ModalSource W) : Decidable s.IsDecision := by
  cases s <;> simp only [ModalSource.IsDecision] <;> infer_instance

/-- The anchoring function of a source assignment, defined on the events with a source. -/
def anchoring (src : Event → Option (ModalSource W)) (e : Event) : Option (ConvBackground W) :=
  (src e).map ModalSource.background

/-- The definedness condition a modal item imposes on its anchor admits any source or only the
decision of a volitional event. -/
inductive AnchorConstraint
  | unrestricted
  | volitionalOnly
  deriving DecidableEq, Repr

/-- The constraint admits the source. -/
def AnchorConstraint.Admits : AnchorConstraint → ModalSource W → Prop
  | .unrestricted, _ => True
  | .volitionalOnly, s => s.IsDecision

instance (c : AnchorConstraint) (s : ModalSource W) : Decidable (c.Admits s) := by
  cases c <;> simp only [AnchorConstraint.Admits] <;> infer_instance

end Modality
