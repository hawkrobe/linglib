import Linglib.Semantics.Modality.ModalTypes

/-!
# Mandarin Modal Inventory

Modal expressions from Mandarin (Sino-Tibetan), based on
[qing-uegaki-2025].

Mandarin has many modals, extensive synonymy, but all satisfy IFF.
-/

namespace Mandarin.Modals

open Modality (ForceFlavor ModalItem)

private abbrev ne : ForceFlavor := (.necessity, .epistemic)
private abbrev pe : ForceFlavor := (.possibility, .epistemic)
private abbrev nd : ForceFlavor := (.necessity, .deontic)
private abbrev nc : ForceFlavor := (.necessity, .circumstantial)
private abbrev pd : ForceFlavor := (.possibility, .deontic)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def yiding : ModalItem := { form := "yīdìng", meaning := {ne} }
def biran : ModalItem := { form := "bìrán", meaning := {ne} }
def juedui : ModalItem := { form := "juéduì", meaning := {ne} }
def bixu : ModalItem := { form := "bìxū", meaning := {nd, nc} }
def yao : ModalItem := { form := "yào", meaning := {nd, nc} }
def dei : ModalItem := { form := "děi", meaning := {nd, nc} }
def yinggai : ModalItem := { form := "yīnggāi", meaning := {ne, nd, nc} }
def dagai : ModalItem := { form := "dàgài", meaning := {ne} }
def keneng : ModalItem := { form := "kěnéng", meaning := {pe} }
def keyi : ModalItem := { form := "kěyǐ", meaning := {pd, pc} }
def yexu : ModalItem := { form := "yěxǔ", meaning := {pe} }
def neng : ModalItem := { form := "néng", meaning := {pd, pc} }

def allExpressions : List ModalItem :=
  [yiding, biran, juedui, bixu, yao, dei, yinggai, dagai, keneng, keyi, yexu, neng]

end Mandarin.Modals
