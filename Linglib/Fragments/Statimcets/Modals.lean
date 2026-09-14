import Linglib.Semantics.Modality.ModalTypes

/-!
# St'át'imcets (Lillooet Salish) Modal Inventory

[matthewson-2016] [rullmann-matthewson-davis-2008]

St'át'imcets (ISO 639-3 `lil`, also known as Lillooet) modal system.
The system demonstrates two key typological properties:

1. **Single morpheme, multiple forces**: the enclitic *=ka* can express
   either deontic permission or obligation depending on context
   ([matthewson-2016] example 1).
2. **Dedicated ability morpheme**: the circumfix *ka-...-a* is
   restricted to ability/circumstantial possibility, contrasting with
   the force-variable *=ka* ([matthewson-2005]).
3. **Lexicalized epistemic/circumstantial split**: epistemic and
   circumstantial modality are expressed by distinct morphological
   strategies. Epistemic modals are typically second-position clitics
   (*ima*, *gat*-type elements, shared with related Salish languages),
   while circumstantial modals are predicative verbs or circumfixes.

## St'át'imcets modal expressions (from [rullmann-matthewson-davis-2008])

| Form       | Type        | Flavour        | Force            |
|-----------|-------------|----------------|------------------|
| =ka       | enclitic    | deontic        | poss + nec       |
| ka-...-a  | circumfix   | circumstantial | possibility      |
-/

namespace Statimcets.Modals

open Modality (ForceFlavor ForceAnalysis ModalItem)

private abbrev nd : ForceFlavor := (.necessity, .deontic)
private abbrev pd : ForceFlavor := (.possibility, .deontic)
private abbrev pc : ForceFlavor := (.possibility, .circumstantial)

/-! ## Modal expressions -/

/-- Deontic enclitic: variable force (permission or obligation).
    [matthewson-2016] example 1:
    - *wá7=ka s-lep' i=k'ún7=a ku=pála7 máqa7*
      'The eggs can/have to stay in the ground for a year.' -/
def ka : ModalItem := { form := "=ka", meaning := {pd, nd} }

/-- Ability circumfix: fixed possibility force, circumstantial flavour.
    [matthewson-2005]:
    - *ka-xílh-ts-tal'í-ha* 'could do it the fastest' -/
def kaCircumfix : ModalItem := { form := "ka-...-a", meaning := {pc} }

def allExpressions : List ModalItem := [ka, kaCircumfix]

/-! ## Force analysis -/

/-- =ka is variable-force (single deontic flavour, both forces).
    ka-...-a is fixed possibility. -/
def forceAnalysis : ModalItem → ForceAnalysis
  | ⟨"=ka", _, _⟩ => .variableForce
  | ⟨"ka-...-a", _, _⟩ => .fixed .possibility
  | _ => .fixed .possibility

/-! ## Background classification

Both St'át'imcets modals formalized here are factual-circumstantial:
=ka is deontic (norms as ordering source) and ka-...-a is ability
(circumstantial facts). The factual-evidential and content-evidential
classes in St'át'imcets are expressed by the evidential elements k'a
and lákw7a, which are not formalized here. -/

open Modality (BackgroundClass) in
def backgroundClass : ModalItem → BackgroundClass
  | _ => .factualCircumstantial

end Statimcets.Modals
