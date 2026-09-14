import Linglib.Semantics.Modality.Basic

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

## Key data ([deal-2011] pp. 574)

(39) *hi-wqii-cix-∅ 'iléxni hipt ke yox hi-pá-ap-o'qa*
     'They are throwing away a lot of food that they could eat.'
     / 'They are throwing away a lot of food that they should eat.'

(40) *hi-wqii-cix-∅ 'óykala hipt ke yox hi-pá-ap-o'qa*
     'They are throwing away all the food that they could eat.'
     (i) ✓ 'They are throwing away all their food. They are eating all
         their food.'
     (ii) # 'They are throwing away all the food they should eat
          (but keeping some junk food).'

In downward-entailing environments (40), *o'qa* behaves only as a
possibility modal — the negated-necessity reading is unavailable.
This parallels how English *some* fails to implicate *not all* under
downward-entailing operators.

## Analysis

[deal-2011]: *o'qa* is a possibility modal acceptable in
non-downward-entailing necessity contexts because there is no
contrasting necessity modal to induce a scalar implicature.
The system parallels what English nominal quantification would look
like with *some* but no *all* or *every*.
-/

namespace NezPerce.Modals

open Modality (ForceFlavor ForceAnalysis ModalItem)

private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

/-! ## Modal expressions -/

/-- Circumstantial possibility modal, pragmatically strengthened in
    non-downward-entailing contexts due to absence of a necessity dual.
    [deal-2011]: pure possibility semantics (∃-quantifier over
    circumstantially accessible worlds). Apparent necessity readings
    are scalar: no ∀-competitor triggers the 'not all' implicature. -/
def oqa : ModalItem := { form := "o'qa", meaning := {pc} }

def allExpressions : List ModalItem := [oqa]

/-! ## Force analysis -/

/-- Force analysis: o'qa is a strengthened possibility modal — base
    semantics is ◇, but absence of a dual ∀-modal allows pragmatic
    necessity readings in non-downward-entailing contexts.
    [matthewson-2016] §18.3.2. -/
def forceAnalysis : ModalItem → ForceAnalysis
  | ⟨"o'qa", _, _⟩ => .strengthened .possibility
  | _ => .strengthened .possibility

end NezPerce.Modals
