module

public import Linglib.Semantics.Modality.Basic

/-!
# Javanese-Paciran Modal Inventory

Modal expressions from Javanese (Austronesian), based on
[vander-klok-2013a].
-/

@[expose] public section

namespace Javanese

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev nc : ForceFlavor := (.necessity, .circumstantial)
abbrev pd : ForceFlavor := (.possibility, .deontic)
abbrev pc : ForceFlavor := (.possibility, .circumstantial)
-- Weak necessity: strong modal + NE marker ([agha-jeretic-2022] §5.2)
abbrev wne : ForceFlavor := (.weakNecessity, .epistemic)
abbrev wnd : ForceFlavor := (.weakNecessity, .deontic)
abbrev wnc : ForceFlavor := (.weakNecessity, .circumstantial)

/-- Strong epistemic necessity *mesthi*. -/
def mesthi : ModalItem := { form := "mesthi", meaning := {ne} }

/-- Weak epistemic necessity *mesthi-ne*: *mesthi* + NE definiteness marker.
    NE picks out the unique minimal witness set (= X operator of
    [agha-jeretic-2022] §5.1), yielding a definite plurality of worlds
    rather than universal quantification. -/
def mesthiNe : ModalItem := { form := "mesthi-ne", meaning := {wne} }

def paleng : ModalItem := { form := "paleng", meaning := {pe} }
def oleh : ModalItem := { form := "oleh", meaning := {pd} }
def iso : ModalItem := { form := "iso", meaning := {pc} }

/-- Strong deontic/circumstantial necessity *kudu*. -/
def kudu1 : ModalItem := { form := "kudu1", meaning := {nd, nc} }

/-- Weak deontic/circumstantial necessity *kudu-ne*: *kudu* + NE.
    Same derivation as *mesthi-ne*: NE = X restricts to necessity
    because ∀ has a unique minimal witness but ∃ does not. -/
def kudu1Ne : ModalItem := { form := "kudu1-ne", meaning := {wnd, wnc} }

def modals : List ModalItem :=
  [mesthi, mesthiNe, paleng, oleh, iso, kudu1, kudu1Ne]

end Javanese
