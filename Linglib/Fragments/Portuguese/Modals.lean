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

private def cp (fos : List ModalForce) (fls : List ModalFlavor) : List ForceFlavor :=
  ForceFlavor.cartesianProduct fos fls

private def allFlavors : List ModalFlavor := ModalFlavor.all

/-! ### Present tense -/

/-- *pode* 'can/may' — possibility modal, all flavors. -/
def poder : ModalItem where
  form := "pode"
  meaning := cp [.possibility] allFlavors

/-- *deve* 'ought/should' — weak necessity modal, all flavors. -/
def dever : ModalItem where
  form := "deve"
  meaning := cp [.weakNecessity] allFlavors

/-- *tem que* 'must/have to' — strong necessity modal, all flavors. -/
def terQue : ModalItem where
  form := "tem que"
  meaning := cp [.necessity] allFlavors

/-! ### Past imperfect -/

/-- *podia* 'could/might', past imperfect — possibility, all flavors. -/
def podia : ModalItem where
  form := "podia"
  meaning := cp [.possibility] allFlavors

/-- *devia* 'ought', past imperfect — weak necessity, all flavors. -/
def devia : ModalItem where
  form := "devia"
  meaning := cp [.weakNecessity] allFlavors

/-- *tinha que* 'had to', past imperfect — strong necessity, all flavors. -/
def tinhaQue : ModalItem where
  form := "tinha que"
  meaning := cp [.necessity] allFlavors

end Portuguese.Modals
