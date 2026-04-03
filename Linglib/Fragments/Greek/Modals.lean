import Linglib.Theories.Semantics.Modality.Typology

/-!
# Modern Greek Modal Inventory

Modal expressions from Modern Greek (Indo-European), based on
@cite{qing-uegaki-2025}.

Greek has non-IFF modals: Prepei and Mporei express non-rectangular
subsets of the meaning space.
-/

namespace Fragments.Greek.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

/-- NOT IFF: forces={nec,poss}, flavors={e,d,c} but missing (poss,d) and (poss,c). -/
def prepei : ModalExpression := ⟨"Prepei", [ne, pe, nd, nc]⟩
/-- NOT IFF: missing (nec,d). -/
def mporei : ModalExpression := ⟨"Mporei", [ne, pe, pd, nc, pc]⟩
def isos : ModalExpression := ⟨"Isos", [pe]⟩

def allExpressions : List ModalExpression :=
  [prepei, mporei, isos]

end Fragments.Greek.Modals
