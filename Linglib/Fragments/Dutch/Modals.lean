import Linglib.Semantics.Modality.Basic

/-!
# Dutch Modal Inventory

Modal expressions from Dutch (Indo-European), based on
[qing-uegaki-2025].

Dutch has one non-IFF modal: zou/zouden...kunnen expresses
{(nec,e),(poss,e),(poss,c)} which is not Cartesian-closed.
-/

namespace Dutch

open Modality (ForceFlavor ModalItem)

private abbrev ne : ForceFlavor := (.necessity, .epistemic)
private abbrev pe : ForceFlavor := (.possibility, .epistemic)
private abbrev nd : ForceFlavor := (.necessity, .deontic)
private abbrev nc : ForceFlavor := (.necessity, .circumstantial)
private abbrev pd : ForceFlavor := (.possibility, .deontic)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

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
