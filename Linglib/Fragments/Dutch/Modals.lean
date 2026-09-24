module

public import Linglib.Semantics.Modality.Basic

/-!
# Dutch modals

The Dutch modal expressions of Uegaki and Hannon's elicited dataset of force-flavour combinations,
distributed with the modal typology database of [guo-imel-steinert-threlkeld-2022]. Under the
projection below, *zou/zouden ... kunnen* is the one expression whose force and flavor are not
independent: it expresses epistemic necessity and epistemic and circumstantial possibility, but not
circumstantial necessity.

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

namespace Dutch

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def zal : ModalItem := { form := "zal", meaning := {ne} }
def moetMoeten : ModalItem := { form := "moet/moeten", meaning := {ne, nd, nc} }
def zouMoeten : ModalItem := { form := "zou/zouden...moeten", meaning := {nd, nc} }
def kanKunnen : ModalItem := { form := "kan/kunnen", meaning := {pc} }
/-- NOT IFF: {(nec,e),(poss,e),(poss,c)} missing (nec,c). -/
def zouKunnen : ModalItem := { form := "zou/zouden...kunnen", meaning := {ne, pe, pc} }
def waarschijnlijk : ModalItem := { form := "waarschijnlijk", meaning := {ne, pe} }
def zalWaarschijnlijk : ModalItem := { form := "zal/zouden waarschijnlijk", meaning := {ne} }
def moetEigenlijk : ModalItem := { form := "moet/moeten eigenlijk", meaning := {nd} }
def misschien : ModalItem := { form := "misschien", meaning := {pe} }
def magMogen : ModalItem := { form := "mag/mogen", meaning := {pd} }

def modals : List ModalItem :=
  [zal, moetMoeten, zouMoeten, kanKunnen, zouKunnen, waarschijnlijk,
   zalWaarschijnlijk, moetEigenlijk, misschien, magMogen]

end Dutch
