import Linglib.Theories.Semantics.Modality.Typology

/-!
# Mandarin Modal Inventory

Modal expressions from Mandarin (Sino-Tibetan), based on
@cite{qing-uegaki-2025}.

Mandarin has many modals, extensive synonymy, but all satisfy IFF.
-/

namespace Fragments.Mandarin.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev nc := ForceFlavor.mk .necessity .circumstantial
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

def yiding : ModalExpression := ⟨"yīdìng", [ne]⟩
def biran : ModalExpression := ⟨"bìrán", [ne]⟩
def juedui : ModalExpression := ⟨"juéduì", [ne]⟩
def bixu : ModalExpression := ⟨"bìxū", [nd, nc]⟩
def yao : ModalExpression := ⟨"yào", [nd, nc]⟩
def dei : ModalExpression := ⟨"děi", [nd, nc]⟩
def yinggai : ModalExpression := ⟨"yīnggāi", [ne, nd, nc]⟩
def dagai : ModalExpression := ⟨"dàgài", [ne]⟩
def keneng : ModalExpression := ⟨"kěnéng", [pe]⟩
def keyi : ModalExpression := ⟨"kěyǐ", [pd, pc]⟩
def yexu : ModalExpression := ⟨"yěxǔ", [pe]⟩
def neng : ModalExpression := ⟨"néng", [pd, pc]⟩

def allExpressions : List ModalExpression :=
  [yiding, biran, juedui, bixu, yao, dei, yinggai, dagai, keneng, keyi, yexu, neng]

end Fragments.Mandarin.Modals
