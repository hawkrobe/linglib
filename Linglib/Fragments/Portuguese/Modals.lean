import Linglib.Semantics.Modality.ModalTypes

/-!
# Portuguese modal verbs

The six modal forms of Brazilian Portuguese as `ModalItem`s: three forces — possibility
*poder*, weak necessity *dever*, strong necessity *ter que* — each in the present and in the
past imperfect, which carries the same force ([ferreira-2023]).

## References

* [ferreira-2023]
-/

namespace Portuguese.Modals

open Modality

/-! ### Present tense -/

/-- *pode* 'can/may' — possibility modal, all flavors. -/
def poder : ModalItem where
  form := "pode"
  meaning := {.possibility} ×ˢ Finset.univ

/-- *deve* 'ought/should' — weak necessity modal, all flavors. -/
def dever : ModalItem where
  form := "deve"
  meaning := {.weakNecessity} ×ˢ Finset.univ

/-- *tem que* 'must/have to' — strong necessity modal, all flavors. -/
def terQue : ModalItem where
  form := "tem que"
  meaning := {.necessity} ×ˢ Finset.univ

/-! ### Past imperfect -/

/-- *podia* 'could/might', past imperfect — possibility, all flavors. -/
def podia : ModalItem where
  form := "podia"
  meaning := {.possibility} ×ˢ Finset.univ

/-- *devia* 'ought', past imperfect — weak necessity, all flavors. -/
def devia : ModalItem where
  form := "devia"
  meaning := {.weakNecessity} ×ˢ Finset.univ

/-- *tinha que* 'had to', past imperfect — strong necessity, all flavors. -/
def tinhaQue : ModalItem where
  form := "tinha que"
  meaning := {.necessity} ×ˢ Finset.univ

end Portuguese.Modals
