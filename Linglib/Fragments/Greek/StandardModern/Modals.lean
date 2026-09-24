module

public import Linglib.Semantics.Modality.Basic

/-!
# Modern Greek modals

The Modern Greek modal expressions of Uegaki and Hannon's elicited dataset of force-flavour
combinations, distributed with the modal typology database of [guo-imel-steinert-threlkeld-2022].
Under the projection below, neither *prepei* nor *mporei* has independent force and flavor: *prepei*
expresses necessity of every flavor but only epistemic possibility, and *mporei* possibility of
every flavor but not deontic necessity.

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

namespace Greek.StandardModern

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

/-- NOT IFF: forces={nec,poss}, flavors={e,d,c} but missing (poss,d) and (poss,c). -/
def prepei : ModalItem := { form := "Prepei", meaning := {ne, pe, nd, nc} }
/-- NOT IFF: missing (nec,d). -/
def mporei : ModalItem := { form := "Mporei", meaning := {ne, pe, pd, nc, pc} }
def isos : ModalItem := { form := "Isos", meaning := {pe} }

def modals : List ModalItem :=
  [prepei, mporei, isos]

end Greek.StandardModern
