import Linglib.Semantics.Modality.Basic

/-!
# Korean modals

The Korean modal expressions of Qing and Uegaki's survey with the forces and flavours each
expresses: the epistemic necessity suffixes *-napo-*, *-keyss-*, *ke-* and *they-*, the
deontic and circumstantial necessity of *-ya ha-* and *-ya keyss-*, the circumstantial *kes.i
coh-*, and the possibility expressions *ci(-to) molun-*, *swu(-to) iss-* and *-to toy-*.

## References

* [qing-uegaki-2025]
-/

namespace Korean

open Modality (ForceFlavor ModalItem)

private abbrev ne : ForceFlavor := (.necessity, .epistemic)
private abbrev pe : ForceFlavor := (.possibility, .epistemic)
private abbrev nd : ForceFlavor := (.necessity, .deontic)
private abbrev nc : ForceFlavor := (.necessity, .circumstantial)
private abbrev pd : ForceFlavor := (.possibility, .deontic)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

def napo : ModalItem := { form := "-napo-", meaning := {ne} }
def keyss : ModalItem := { form := "-keyss-", meaning := {ne} }
def yaHa : ModalItem := { form := "-ya + ha-", meaning := {nd, nc} }
def ke : ModalItem := { form := "ke-", meaning := {ne} }
def they : ModalItem := { form := "they-", meaning := {ne} }
def yaKeyss : ModalItem := { form := "-ya + keyss-", meaning := {nd} }
def kesiCoh : ModalItem := { form := "kes.i-coh-", meaning := {nc} }
def ciMolun : ModalItem := { form := "ci(-to) molun-", meaning := {pe} }
def swuIss : ModalItem := { form := "swu(-to) iss-", meaning := {pe, pc} }
def toToy : ModalItem := { form := "-to + toy-", meaning := {pd, pc} }

def modals : List ModalItem :=
  [napo, keyss, yaHa, ke, they, yaKeyss, kesiCoh, ciMolun, swuIss, toToy]

end Korean
