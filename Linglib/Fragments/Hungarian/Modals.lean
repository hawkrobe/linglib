import Linglib.Semantics.Modality.Basic

/-!
# Hungarian Modal Inventory

Modal expressions from Hungarian (Uralic), based on
[qing-uegaki-2025].
-/

namespace Hungarian.Modals

open Modality (ForceFlavor ModalItem)

private abbrev ne : ForceFlavor := (.necessity, .epistemic)
private abbrev pe : ForceFlavor := (.possibility, .epistemic)
private abbrev nd : ForceFlavor := (.necessity, .deontic)
private abbrev nc : ForceFlavor := (.necessity, .circumstantial)
private abbrev pd : ForceFlavor := (.possibility, .deontic)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def kell : ModalItem := { form := "kell", meaning := {ne, nd, nc} }
def kellene : ModalItem := { form := "kellene", meaning := {nd, nc} }
def muszáj : ModalItem := { form := "muszáj", meaning := {nd, nc} }
def valószínűleg : ModalItem := { form := "valószínűleg", meaning := {ne} }
def lehet : ModalItem := { form := "lehet", meaning := {pe} }
def hatHet : ModalItem := { form := "-hat/-het", meaning := {pe, pd, pc} }
def tud : ModalItem := { form := "tud-", meaning := {pc} }
def kép : ModalItem := { form := "kép-", meaning := {pc} }

def allExpressions : List ModalItem :=
  [kell, kellene, muszáj, valószínűleg, lehet, hatHet, tud, kép]

end Hungarian.Modals
