module

public import Linglib.Semantics.Modality.Basic

/-!
# Modern Greek Modal Inventory

Modal expressions from Modern Greek (Indo-European), based on
[qing-uegaki-2025].

Greek has non-IFF modals: Prepei and Mporei express non-rectangular
subsets of the meaning space.
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
