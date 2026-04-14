import Linglib.Theories.Semantics.Modality.Typology

/-!
# St'át'imcets (Lillooet Salish) Modal Inventory

@cite{matthewson-2016} @cite{rullmann-matthewson-davis-2008}

St'át'imcets (ISO 639-3 `lil`, also known as Lillooet) modal system.
The system demonstrates two key typological properties:

1. **Single morpheme, multiple forces**: the enclitic *=ka* can express
   either deontic permission or obligation depending on context
   (@cite{matthewson-2016} example 1).
2. **Dedicated ability morpheme**: the circumfix *ka-...-a* is
   restricted to ability/circumstantial possibility, contrasting with
   the force-variable *=ka* (@cite{matthewson-2005}).
3. **Lexicalized epistemic/circumstantial split**: epistemic and
   circumstantial modality are expressed by distinct morphological
   strategies. Epistemic modals are typically second-position clitics
   (*ima*, *gat*-type elements, shared with related Salish languages),
   while circumstantial modals are predicative verbs or circumfixes.

## St'át'imcets modal expressions (from @cite{rullmann-matthewson-davis-2008})

| Form       | Type        | Flavour        | Force            |
|-----------|-------------|----------------|------------------|
| =ka       | enclitic    | deontic        | poss + nec       |
| ka-...-a  | circumfix   | circumstantial | possibility      |
-/

namespace Fragments.Statimcets.Modals

open Core.Modality (ForceFlavor ForceAnalysis)
open Semantics.Modality.Typology (ModalExpression satisfiesIFF satisfiesSAV)

private abbrev nd := ForceFlavor.mk .necessity .deontic
private abbrev pd := ForceFlavor.mk .possibility .deontic
private abbrev pc := ForceFlavor.mk .possibility .circumstantial

/-! ## Modal expressions -/

/-- Deontic enclitic: variable force (permission or obligation).
    @cite{matthewson-2016} example 1:
    - *wá7=ka s-lep' i=k'ún7=a ku=pála7 máqa7*
      'The eggs can/have to stay in the ground for a year.' -/
def ka : ModalExpression := ⟨"=ka", [pd, nd]⟩

/-- Ability circumfix: fixed possibility force, circumstantial flavour.
    @cite{matthewson-2005}:
    - *ka-xílh-ts-tal'í-ha* 'could do it the fastest' -/
def kaCircumfix : ModalExpression := ⟨"ka-...-a", [pc]⟩

def allExpressions : List ModalExpression := [ka, kaCircumfix]

/-! ## Force analysis -/

/-- =ka is variable-force (single deontic flavour, both forces).
    ka-...-a is fixed possibility. -/
def forceAnalysis : ModalExpression → ForceAnalysis
  | ⟨"=ka", _⟩ => .variableForce
  | ⟨"ka-...-a", _⟩ => .fixed .possibility
  | _ => .fixed .possibility

/-! ## Background classification

Both St'át'imcets modals formalized here are factual-circumstantial:
=ka is deontic (norms as ordering source) and ka-...-a is ability
(circumstantial facts). The factual-evidential and content-evidential
classes in St'át'imcets are expressed by the evidential elements k'a
and lákw7a, which are not formalized here. -/

open Core.Modality (BackgroundClass) in
def backgroundClass : ModalExpression → BackgroundClass
  | _ => .factualCircumstantial

/-! ## Typological properties -/

/-- =ka satisfies IFF (trivially: single flavour, variable force =
    Cartesian product {poss, nec} × {deontic}). -/
theorem ka_satisfies_iff : satisfiesIFF ka.meaning = true := by decide

/-- =ka satisfies SAV: varies on force axis only. -/
theorem ka_satisfies_sav : satisfiesSAV ka.meaning = true := by decide

/-- ka-...-a satisfies IFF (singleton meaning). -/
theorem kaCircumfix_satisfies_iff :
    satisfiesIFF kaCircumfix.meaning = true := by decide

/-- All St'át'imcets modals satisfy IFF. -/
theorem all_satisfy_iff :
    allExpressions.all (fun e => satisfiesIFF e.meaning) = true := by decide

end Fragments.Statimcets.Modals
