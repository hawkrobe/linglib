module

public import Linglib.Semantics.Modality.Basic

/-!
# Nez Perce Modal Inventory

[deal-2011] [matthewson-2016]

Nez Perce (Sahaptian, ISO 639-3 `nez`) circumstantial modal system.
Nez Perce is a key example of a language with **modals without duals**
([matthewson-2016] §18.3.2): the circumstantial modal *o'qa* is
a possibility modal that appears to have both possibility and necessity
readings, but [deal-2011] argues it is semantically a pure
possibility modal whose apparent necessity readings arise from the
absence of a contrasting necessity modal.

## Key data ([deal-2011] (51)–(52), p. 574; [matthewson-2016] (39)–(40))

(51) *hi-wqíi-cix-∅ 'iléx̂ni hipt ke yox̂ hi-pá-ap-o'qa*
     a. 'They are throwing away a lot of food that they could eat.'
     b. 'They are throwing away a lot of food that they should eat.'

(52) *hi-wqíi-cix-∅ 'óykala hipt ke yox̂ hi-pá-ap-o'qa*
     a. 'They are throwing away all the food that they could eat. They are
        throwing away all their food.'
     b. # 'They are throwing away all the food that they should eat (but
        keeping some junk food).'

In downward-entailing environments such as the restriction of 'óykala 'all' in (52), *o'qa*
behaves only as a possibility modal — the necessity translation is unavailable.
This parallels how English *some* fails to implicate *not all* under
downward-entailing operators.

## Analysis

[deal-2011]: *o'qa* is a possibility modal acceptable in
non-downward-entailing necessity contexts because there is no
contrasting necessity modal to induce a scalar implicature.
The system parallels what English nominal quantification would look
like with *some* but no *all* or *every*.
-/

@[expose] public section

namespace NezPerce

open Modality (ForceFlavor ModalItem)

abbrev pc : ForceFlavor := (.possibility, .circumstantial)

/-! ## Modal expressions -/

/-- Circumstantial possibility modal without a necessity dual. [deal-2011]: a pure possibility
    modal (∃ over circumstantially accessible worlds) outside any Horn scale, so no scalar
    implicature keeps it out of necessity contexts in upward-entailing environments. -/
def oqa : ModalItem := { form := "o'qa", meaning := {pc} }

def modals : List ModalItem := [oqa]

end NezPerce
