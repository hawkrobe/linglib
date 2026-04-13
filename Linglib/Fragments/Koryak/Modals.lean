import Linglib.Theories.Semantics.Modality.Typology

/-!
# Koryak Modal Inventory

Modal expressions from Koryak (Chukotko-Kamchatkan), based on
@cite{mocnik-abramovitz-2019}.

Koryak is a key counterexample to the SAV universal (@cite{nauze-2008}):
the attitude verb *ivək* expresses both necessity and possibility with
both doxastic and assertive flavors, varying on **both** axes.

In the 3×3 space, doxastic maps to epistemic and assertive maps to
epistemic (both are knowledge/belief-oriented), so *ivək*'s meaning
reduces to variable-force epistemic, which satisfies both SAV and IFF.
However, following @cite{steinert-threlkeld-imel-guo-2023} §4.1, the
relevant observation is that *ivək* varies on both force and flavor
when the flavor axis is taken at full granularity (doxastic ≠ assertive).

We encode the 3×3-projected meaning here. The full doxastic/assertive
distinction requires a finer-grained flavor type than `ModalFlavor`.
-/

namespace Fragments.Koryak.Modals

open Core.Modality (ForceFlavor)
open Semantics.Modality.Typology (ModalExpression)

private abbrev ne := ForceFlavor.mk .necessity .epistemic
private abbrev pe := ForceFlavor.mk .possibility .epistemic

/-- *ivək* — variable-force attitude verb.
    Doxastic: 'believe' (necessity) / 'allow for the possibility that' (possibility).
    Assertive: 'say/assert' (necessity) / assertive possibility.
    Both doxastic and assertive map to epistemic in the 3×3 space. -/
def modalIvek : ModalExpression := { form := "ivək", meaning := [ne, pe] }

def allExpressions : List ModalExpression := [modalIvek]

end Fragments.Koryak.Modals
