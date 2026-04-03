import Linglib.Theories.Semantics.Modality.Typology

/-!
# Dutch Modal Inventory

Modal expressions from Dutch (Indo-European), based on
@cite{qing-uegaki-2025}.

Dutch has one non-IFF modal: zou/zouden...kunnen expresses
{(nec,e),(poss,e),(poss,c)} which is not Cartesian-closed.
-/

namespace Fragments.Dutch.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

def zal : ModalExpression := ⟨"zal", [ne]⟩
def moetMoeten : ModalExpression := ⟨"moet/moeten", [ne, nd, nc]⟩
def zouMoeten : ModalExpression := ⟨"zou/zouden...moeten", [nd, nc]⟩
def kanKunnen : ModalExpression := ⟨"kan/kunnen", [pc]⟩
/-- NOT IFF: {(nec,e),(poss,e),(poss,c)} missing (nec,c). -/
def zouKunnen : ModalExpression := ⟨"zou/zouden...kunnen", [ne, pe, pc]⟩
def waarschijnlijk : ModalExpression := ⟨"waarschijnlijk", [ne, pe]⟩
def zalWaarschijnlijk : ModalExpression := ⟨"zal/zouden waarschijnlijk", [ne]⟩
def moetEigenlijk : ModalExpression := ⟨"moet/moeten eigenlijk", [nd]⟩
def misschien : ModalExpression := ⟨"misschien", [pe]⟩
def magMogen : ModalExpression := ⟨"mag/mogen", [pd]⟩

def allExpressions : List ModalExpression :=
  [zal, moetMoeten, zouMoeten, kanKunnen, zouKunnen, waarschijnlijk,
   zalWaarschijnlijk, moetEigenlijk, misschien, magMogen]

end Fragments.Dutch.Modals
