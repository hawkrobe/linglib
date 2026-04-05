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
-- Weak necessity: strong modal + NE marker (@cite{agha-jeretic-2022} §5.2)
private abbrev wne := ForceFlavor.mk .weakNecessity .epistemic
private abbrev wnd := ForceFlavor.mk .weakNecessity .deontic
private abbrev wnc := ForceFlavor.mk .weakNecessity .circumstantial

/-- Strong epistemic necessity *mesthi*. -/
def mesthi : ModalExpression := ⟨"mesthi", [ne]⟩

/-- Weak epistemic necessity *mesthi-ne*: *mesthi* + NE definiteness marker.
    NE picks out the unique minimal witness set (= X operator of
    @cite{agha-jeretic-2022} §5.1), yielding a definite plurality of worlds
    rather than universal quantification. -/
def mesthiNe : ModalExpression := ⟨"mesthi-ne", [wne]⟩

def paleng : ModalExpression := ⟨"paleng", [pe]⟩
def oleh : ModalExpression := ⟨"oleh", [pd]⟩
def iso : ModalExpression := ⟨"iso", [pc]⟩

/-- Strong deontic/circumstantial necessity *kudu*. -/
def kudu1 : ModalExpression := ⟨"kudu1", [nd, nc]⟩

/-- Weak deontic/circumstantial necessity *kudu-ne*: *kudu* + NE.
    Same derivation as *mesthi-ne*: NE = X restricts to necessity
    because ∀ has a unique minimal witness but ∃ does not. -/
def kudu1Ne : ModalExpression := ⟨"kudu1-ne", [wnd, wnc]⟩

def allExpressions : List ModalExpression :=
  [mesthi, mesthiNe, paleng, oleh, iso, kudu1, kudu1Ne]

end Fragments.Javanese.Modals
