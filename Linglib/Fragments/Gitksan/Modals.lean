import Linglib.Theories.Semantics.Modality.Typology

/-!
# Gitksan Modal Inventory

Modal expressions from Gitksan (Tsimshian), based on
@cite{matthewson-2013}.

Gitksan has variable-force modals: ima('a) and gat express both
weak and strong epistemic force.
-/

namespace Fragments.Gitksan.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

/-- Variable-force epistemic modal. -/
def imaa : ModalExpression := ⟨"ima('a)", [pe, ne]⟩
/-- Variable-force epistemic modal (+ reportative → epistemic). -/
def gat : ModalExpression := ⟨"gat", [pe, ne]⟩
def daakhlxw : ModalExpression := ⟨"da'akhlxw", [pc]⟩
def anookxw : ModalExpression := ⟨"anook(xw)", [pd]⟩
def sgi : ModalExpression := ⟨"sgi", [nd, nc]⟩

def allExpressions : List ModalExpression :=
  [imaa, gat, daakhlxw, anookxw, sgi]

end Fragments.Gitksan.Modals
