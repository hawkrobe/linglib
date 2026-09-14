import Linglib.Semantics.Modality.ModalTypes

/-!
# Tlingit Modal Inventory

Modal expressions from Tlingit (Athabaskan-Eyak-Tlingit), based on
[cable-2017].
-/

namespace Tlingit.Modals

open Modality (ForceFlavor ModalItem)

private abbrev pe : ForceFlavor := (.possibility, .epistemic)
private abbrev nc : ForceFlavor := (.necessity, .circumstantial)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def gwal : ModalItem := { form := "gwal", meaning := {pe} }
def giwe : ModalItem := { form := "giwe", meaning := {pe} }
def shákdé : ModalItem := { form := "shákdé", meaning := {pe} }
def futureMode : ModalItem := { form := "future mode", meaning := {nc} }
def potentialMode : ModalItem := { form := "potential mode", meaning := {pc} }

def allExpressions : List ModalItem :=
  [gwal, giwe, shákdé, futureMode, potentialMode]

end Tlingit.Modals
