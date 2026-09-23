module

public import Linglib.Semantics.Modality.Basic

/-!
# Washo Modal Inventory

Modal expressions from Washo (isolate), based on
[bochnak-2015a] and [bochnak-2015b].

Washo is a key counterexample to the SAV universal ([nauze-2008]):
the modal verb *-eʔ* expresses both possibility and necessity with both
epistemic and deontic flavors, varying on **both** axes simultaneously.
Despite this, *-eʔ* satisfies the IFF universal
([steinert-threlkeld-imel-guo-2023]): its meaning is the full
Cartesian product {necessity, possibility} × {epistemic, deontic}.
-/

@[expose] public section

namespace Washo

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev nd : ForceFlavor := (.necessity, .deontic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)
abbrev pd : ForceFlavor := (.possibility, .deontic)

/-- *-eʔ* — variable-force, variable-flavor modal verb.
    Expresses epistemic and deontic modality with both weak and strong force.
    Counterexample to SAV: varies on both axes. Satisfies IFF: the meaning
    is {necessity, possibility} × {epistemic, deontic}. -/
def modalEq : ModalItem := { form := "-eʔ", meaning := {ne, nd, pe, pd} }

def modals : List ModalItem := [modalEq]

end Washo
