import Linglib.Theories.Semantics.Modality.Typology

/-!
# Nez Perce Modal Inventory

@cite{deal-2011} @cite{matthewson-2016}

Nez Perce (Sahaptian, ISO 639-3 `nez`) circumstantial modal system.
Nez Perce is a key example of a language with **modals without duals**
(@cite{matthewson-2016} §18.3.2): the circumstantial modal *o'qa* is
a possibility modal that appears to have both possibility and necessity
readings, but @cite{deal-2011} argues it is semantically a pure
possibility modal whose apparent necessity readings arise from the
absence of a contrasting necessity modal.

## Key data (@cite{deal-2011} pp. 574)

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

@cite{deal-2011}: *o'qa* is a possibility modal acceptable in
non-downward-entailing necessity contexts because there is no
contrasting necessity modal to induce a scalar implicature.
The system parallels what English nominal quantification would look
like with *some* but no *all* or *every*.
-/

namespace Fragments.NezPerce.Modals

open Core.Modality (ForceFlavor ForceAnalysis)
open Semantics.Modality.Typology (ModalExpression satisfiesIFF satisfiesSAV)

private abbrev pc := ForceFlavor.mk .possibility .circumstantial

/-! ## Modal expressions -/

/-- Circumstantial possibility modal, pragmatically strengthened in
    non-downward-entailing contexts due to absence of a necessity dual.
    @cite{deal-2011}: pure possibility semantics (∃-quantifier over
    circumstantially accessible worlds). Apparent necessity readings
    are scalar: no ∀-competitor triggers the 'not all' implicature. -/
def oqa : ModalExpression := ⟨"o'qa", [pc]⟩

def allExpressions : List ModalExpression := [oqa]

/-! ## Force analysis -/

/-- Force analysis: o'qa is a strengthened possibility modal — base
    semantics is ◇, but absence of a dual ∀-modal allows pragmatic
    necessity readings in non-downward-entailing contexts.
    @cite{matthewson-2016} §18.3.2. -/
def forceAnalysis : ModalExpression → ForceAnalysis
  | ⟨"o'qa", _⟩ => .strengthened .possibility
  | _ => .strengthened .possibility

/-- o'qa has no lexical dual. -/
theorem oqa_no_dual : (forceAnalysis oqa).hasDual = false := rfl

/-- o'qa admits necessity readings (via strengthening). -/
theorem oqa_admits_necessity :
    (forceAnalysis oqa).admitsNecessity = true := rfl

/-- o'qa admits possibility readings (base semantics). -/
theorem oqa_admits_possibility :
    (forceAnalysis oqa).admitsPossibility = true := rfl

/-! ## Background classification -/

open Core.Modality (BackgroundClass) in
/-- o'qa is factual-circumstantial: the modal base provides facts about
    the actual world (circumstances), not evidence or information. -/
def backgroundClass : ModalExpression → BackgroundClass
  | _ => .factualCircumstantial

/-! ## Typological properties -/

/-- o'qa satisfies IFF (singleton meaning). -/
theorem oqa_satisfies_iff : satisfiesIFF oqa.meaning = true := by decide

/-- The *semantic* meaning of o'qa (pure possibility) is a singleton,
    so its SAV status reflects the base semantics, not the pragmatically
    enriched interpretation. -/
theorem oqa_satisfies_sav : satisfiesSAV oqa.meaning = true := by decide

end Fragments.NezPerce.Modals
