import Linglib.Theories.Semantics.Modality.Typology

/-!
# Korean Modal Inventory

Modal expressions from Korean (Koreanic), based on
@cite{qing-uegaki-2025}.
-/

namespace Fragments.Korean.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

def napo : ModalExpression := ⟨"-napo-", [ne]⟩
def keyss : ModalExpression := ⟨"-keyss-", [ne]⟩
def yaHa : ModalExpression := ⟨"-ya + ha-", [nd, nc]⟩
def ke : ModalExpression := ⟨"ke-", [ne]⟩
def they : ModalExpression := ⟨"they-", [ne]⟩
def yaKeyss : ModalExpression := ⟨"-ya + keyss-", [nd]⟩
def kesiCoh : ModalExpression := ⟨"kes.i-coh-", [nc]⟩
def ciMolun : ModalExpression := ⟨"ci(-to) molun-", [pe]⟩
def swuIss : ModalExpression := ⟨"swu(-to) iss-", [pe, pc]⟩
def toToy : ModalExpression := ⟨"-to + toy-", [pd, pc]⟩

def allExpressions : List ModalExpression :=
  [napo, keyss, yaHa, ke, they, yaKeyss, kesiCoh, ciMolun, swuIss, toToy]

end Fragments.Korean.Modals
