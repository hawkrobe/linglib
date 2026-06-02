import Linglib.Semantics.Modality.Typology

/-!
# Tlingit Modal Inventory

Modal expressions from Tlingit (Athabaskan-Eyak-Tlingit), based on
[cable-2017].
-/

namespace Tlingit.Modals

open Semantics.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

def gwal : ModalExpression := ⟨"gwal", [pe]⟩
def giwe : ModalExpression := ⟨"giwe", [pe]⟩
def shákdé : ModalExpression := ⟨"shákdé", [pe]⟩
def futureMode : ModalExpression := ⟨"future mode", [nc]⟩
def potentialMode : ModalExpression := ⟨"potential mode", [pc]⟩

def allExpressions : List ModalExpression :=
  [gwal, giwe, shákdé, futureMode, potentialMode]

end Tlingit.Modals
