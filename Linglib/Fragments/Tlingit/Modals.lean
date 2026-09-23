module

public import Linglib.Semantics.Modality.Basic

/-!
# Tlingit Modal Inventory

Modal expressions from Tlingit (Athabaskan-Eyak-Tlingit), based on
[cable-2017].
-/

@[expose] public section

namespace Tlingit

open Modality (ForceFlavor ModalItem)

abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def gwal : ModalItem := { form := "gwal", meaning := {pe} }
def giwe : ModalItem := { form := "giwe", meaning := {pe} }
def shákdé : ModalItem := { form := "shákdé", meaning := {pe} }
def futureMode : ModalItem := { form := "future mode", meaning := {nc} }
def potentialMode : ModalItem := { form := "potential mode", meaning := {pc} }

def modals : List ModalItem :=
  [gwal, giwe, shákdé, futureMode, potentialMode]

end Tlingit
