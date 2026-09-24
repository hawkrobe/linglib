module

public import Linglib.Semantics.Modality.Basic

/-!
# Hungarian modals

The Hungarian modal expressions of Uegaki and Hannon's elicited dataset of force-flavour
combinations, distributed with the modal typology database of [guo-imel-steinert-threlkeld-2022].

## Implementation notes

The dataset records whether each expression is felicitous in contexts of three forces,
necessity, weak necessity and possibility, and five flavors, epistemic, deontic, teleological,
circumstantial and bouletic, with and without negation. An entry's meaning is its
positive-polarity cells judged felicitous, with weak necessity entered as necessity and
teleological as circumstantial; bouletic cells are left out, and so are the expressions with no
other felicitous cell. Whether a meaning has independent force and flavor depends on this
projection.

## References

* [uegaki-hannon-2022]
* [guo-imel-steinert-threlkeld-2022]
-/

@[expose] public section

namespace Hungarian

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def kell : ModalItem := { form := "kell", meaning := {ne, nd, nc} }
def kellene : ModalItem := { form := "kellene", meaning := {nd, nc} }
def muszáj : ModalItem := { form := "muszáj", meaning := {nd, nc} }
def valószínűleg : ModalItem := { form := "valószínűleg", meaning := {ne} }
def lehet : ModalItem := { form := "lehet", meaning := {pe} }
def hatHet : ModalItem := { form := "-hat/-het", meaning := {pe, pd, pc} }
def tud : ModalItem := { form := "tud-", meaning := {pc} }
def kép : ModalItem := { form := "kép-", meaning := {pc} }

def modals : List ModalItem :=
  [kell, kellene, muszáj, valószínűleg, lehet, hatHet, tud, kép]

end Hungarian
