import Linglib.Theories.Semantics.Modality.Typology

/-!
# Javanese-Paciran Modal Inventory

Modal expressions from Javanese (Austronesian), based on
@cite{vander-klok-2013a}.
-/

namespace Fragments.Javanese.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

def mesthi : ModalExpression := ⟨"mesthi", [ne]⟩
def mesthiNe : ModalExpression := ⟨"mesthi-ne", [ne]⟩
def paleng : ModalExpression := ⟨"paleng", [pe]⟩
def oleh : ModalExpression := ⟨"oleh", [pd]⟩
def iso : ModalExpression := ⟨"iso", [pc]⟩
def kudu1 : ModalExpression := ⟨"kudu1", [nd, nc]⟩
def kudu1Ne : ModalExpression := ⟨"kudu1-ne", [nd, nc]⟩

def allExpressions : List ModalExpression :=
  [mesthi, mesthiNe, paleng, oleh, iso, kudu1, kudu1Ne]

end Fragments.Javanese.Modals
