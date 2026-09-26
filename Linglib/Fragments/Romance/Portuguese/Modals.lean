module

public import Linglib.Semantics.Modality.Basic
public import Linglib.Syntax.Category.Auxiliary.Basic

/-!
# Portuguese modal verbs

This file defines the six modal forms of Ferreira's square of necessities as auxiliaries. The
possibility modal *poder*, the weak necessity modal *dever* and the strong necessity modal *ter
que* each appear in the present, *pode*, *deve* and *tem que*, and in the past imperfect,
*podia*, *devia* and *tinha que*, and the past imperfect carries the same force as the present:
*ele devia estar aqui agora, mas não está* 'he ought to be here now, but he isn't' holds where
the present *deve* is odd. The data are Brazilian, and Ferreira reports no relevant difference
from the European variety. Each form takes every flavor, and the tense is the datum the square
reads, the matter of `Studies/Ferreira2023.lean`.

## Main definitions

* `Portuguese.Modals.poder`, `Portuguese.Modals.dever`, `Portuguese.Modals.terQue`: the present
  forms.
* `Portuguese.Modals.podia`, `Portuguese.Modals.devia`, `Portuguese.Modals.tinhaQue`: the past
  imperfect forms.

## References

* [ferreira-2023]
-/

@[expose] public section

namespace Portuguese.Modals

open Modality

/-! ### Present -/

/-- *pode* 'can, may', the present possibility modal. -/
def poder : Auxiliary where
  form := "pode"
  modality := {.possibility} ×ˢ Finset.univ
  features := Morphology.Features.of (tense := some .Pres)

/-- *deve* 'ought, should', the present weak necessity modal. -/
def dever : Auxiliary where
  form := "deve"
  modality := {.weakNecessity} ×ˢ Finset.univ
  features := Morphology.Features.of (tense := some .Pres)

/-- *tem que* 'must, have to', the present strong necessity modal. -/
def terQue : Auxiliary where
  form := "tem que"
  modality := {.necessity} ×ˢ Finset.univ
  features := Morphology.Features.of (tense := some .Pres)

/-! ### Past imperfect -/

/-- *podia* 'could, might', the past imperfect possibility modal. -/
def podia : Auxiliary where
  form := "podia"
  modality := {.possibility} ×ˢ Finset.univ
  features := Morphology.Features.of (tense := some .Imp)

/-- *devia* 'ought', the past imperfect weak necessity modal. -/
def devia : Auxiliary where
  form := "devia"
  modality := {.weakNecessity} ×ˢ Finset.univ
  features := Morphology.Features.of (tense := some .Imp)

/-- *tinha que* 'had to', the past imperfect strong necessity modal. -/
def tinhaQue : Auxiliary where
  form := "tinha que"
  modality := {.necessity} ×ˢ Finset.univ
  features := Morphology.Features.of (tense := some .Imp)

end Portuguese.Modals
