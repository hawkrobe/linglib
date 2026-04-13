import Linglib.Theories.Semantics.Modality.Typology

/-!
# Washo Modal Inventory

Modal expressions from Washo (isolate), based on
@cite{bochnak-2015a} and @cite{bochnak-2015b}.

Washo is a key counterexample to the SAV universal (@cite{nauze-2008}):
the modal verb *-eʔ* expresses both possibility and necessity with both
epistemic and deontic flavors, varying on **both** axes simultaneously.
Despite this, *-eʔ* satisfies the IFF universal
(@cite{steinert-threlkeld-imel-guo-2023}): its meaning is the full
Cartesian product {necessity, possibility} × {epistemic, deontic}.
-/

namespace Fragments.Washo.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev pe := ForceFlavor.mk .possibility .epistemic
private abbrev pd := ForceFlavor.mk .possibility .deontic

/-- *-eʔ* — variable-force, variable-flavor modal verb.
    Expresses epistemic and deontic modality with both weak and strong force.
    Counterexample to SAV: varies on both axes. Satisfies IFF: the meaning
    is {necessity, possibility} × {epistemic, deontic}. -/
def modalEq : ModalExpression := { form := "-eʔ", meaning := [ne, nd, pe, pd] }

def allExpressions : List ModalExpression := [modalEq]

end Fragments.Washo.Modals
