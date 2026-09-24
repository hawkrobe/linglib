module

public import Linglib.Semantics.Modality.Basic

/-!
# Korean modals

The Korean modal expressions of Uegaki and Hannon's elicited dataset of force-flavour combinations,
distributed with the modal typology database of [guo-imel-steinert-threlkeld-2022], with the forces
and flavours each expresses: the epistemic necessity suffixes *-napo-*, *-keyss-*, *ke-* and
*they-*, the deontic and circumstantial necessity of *-ya ha-*, the deontic necessity of *-ya
keyss-*, the circumstantial *kes.i coh-*, and the possibility expressions *ci(-to) molun-*,
*swu(-to) iss-* and *-to toy-*.

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

namespace Korean

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def napo : ModalItem := { form := "-napo-", meaning := {ne} }
def keyss : ModalItem := { form := "-keyss-", meaning := {ne} }
def yaHa : ModalItem := { form := "-ya + ha-", meaning := {nd, nc} }
def ke : ModalItem := { form := "ke-", meaning := {ne} }
def they : ModalItem := { form := "they-", meaning := {ne} }
def yaKeyss : ModalItem := { form := "-ya + keyss-", meaning := {nd} }
def kesiCoh : ModalItem := { form := "kes.i-coh-", meaning := {nc} }
def ciMolun : ModalItem := { form := "ci(-to) molun-", meaning := {pe} }
def swuIss : ModalItem := { form := "swu(-to) iss-", meaning := {pe, pc} }
def toToy : ModalItem := { form := "-to + toy-", meaning := {pd, pc} }

def modals : List ModalItem :=
  [napo, keyss, yaHa, ke, they, yaKeyss, kesiCoh, ciMolun, swuIss, toToy]

end Korean
