module

public import Linglib.Semantics.Modality.Basic

/-!
# Koryak Modal Inventory

Modal expressions from Koryak (Chukotko-Kamchatkan), based on
[mocnik-abramovitz-2019].

Koryak is a key counterexample to the SAV universal ([nauze-2008]):
the attitude verb *ivək* expresses both necessity and possibility with
both doxastic and assertive flavors, varying on **both** axes.

In the 3×3 space, doxastic maps to epistemic and assertive maps to
epistemic (both are knowledge/belief-oriented), so *ivək*'s meaning
reduces to variable-force epistemic, which satisfies both SAV and IFF.
However, following [steinert-threlkeld-imel-guo-2023] §4.1, the
relevant observation is that *ivək* varies on both force and flavor
when the flavor axis is taken at full granularity (doxastic ≠ assertive).

We encode the 3×3-projected meaning here. The full doxastic/assertive
distinction requires a finer-grained flavor type than `ModalFlavor`.
-/

@[expose] public section

namespace Koryak

open Modality (ForceFlavor ModalItem)

abbrev ne : ForceFlavor := (.necessity, .epistemic)
abbrev pe : ForceFlavor := (.possibility, .epistemic)

/-- *ivək* — variable-force attitude verb.
    Doxastic: 'believe' (necessity) / 'allow for the possibility that' (possibility).
    Assertive: 'say/assert' (necessity) / assertive possibility.
    Both doxastic and assertive map to epistemic in the 3×3 space. -/
def modalIvek : ModalItem := { form := "ivək", meaning := {ne, pe} }

def modals : List ModalItem := [modalIvek]

end Koryak
