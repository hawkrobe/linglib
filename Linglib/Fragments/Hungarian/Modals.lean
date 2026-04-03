import Linglib.Theories.Semantics.Modality.Typology

/-!
# Hungarian Modal Inventory

Modal expressions from Hungarian (Uralic), based on
@cite{qing-uegaki-2025}.
-/

namespace Fragments.Hungarian.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

def kell : ModalExpression := ⟨"kell", [ne, nd, nc]⟩
def kellene : ModalExpression := ⟨"kellene", [nd, nc]⟩
def muszáj : ModalExpression := ⟨"muszáj", [nd, nc]⟩
def valószínűleg : ModalExpression := ⟨"valószínűleg", [ne]⟩
def lehet : ModalExpression := ⟨"lehet", [pe]⟩
def hatHet : ModalExpression := ⟨"-hat/-het", [pe, pd, pc]⟩
def tud : ModalExpression := ⟨"tud-", [pc]⟩
def kép : ModalExpression := ⟨"kép-", [pc]⟩

def allExpressions : List ModalExpression :=
  [kell, kellene, muszáj, valószínűleg, lehet, hatHet, tud, kép]

end Fragments.Hungarian.Modals
