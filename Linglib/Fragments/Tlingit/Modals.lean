module

public import Linglib.Semantics.Modality.Basic

/-!
# Tlingit modals

The modal expressions of Tlingit (Athabaskan-Eyak-Tlingit, ISO 639-3 `tli`) that Cable
describes, as coded in the modal typology database of Guo, Imel and Steinert-Threlkeld. Three
expressions, *gwál*, *giwe* and *shákdé*, express epistemic possibility; the future mode of the
verb expresses circumstantial necessity and the potential mode circumstantial possibility.

## Implementation notes

* The database records whether each expression can express each combination of weak or strong
  force with epistemic, deontic or circumstantial flavor, in positive and in negative clauses.
  An entry's meaning is its positive-clause combinations marked expressible, weak force entered
  as possibility and strong as necessity. Combinations marked unknown are left out, and so are
  the prohibitive mode and *tlél aadé … yé*, which the database records only under negation.
* The future and potential modes are inflectional categories of the verb, each realized by a
  combination of prefixes and suffixes, and their entries carry the mode's name as form.

## References

* [cable-2017]
* [guo-imel-steinert-threlkeld-2022]
* [cable-2022]
-/

@[expose] public section

namespace Tlingit

open Modality

/-- The dubitative *gwál*, expressing epistemic possibility. -/
def gwál : ModalItem := { form := "gwál", meaning := {(.possibility, .epistemic)} }

/-- *giwe*, expressing epistemic possibility. -/
def giwe : ModalItem := { form := "giwe", meaning := {(.possibility, .epistemic)} }

/-- *shákdé*, expressing epistemic possibility. -/
def shákdé : ModalItem := { form := "shákdé", meaning := {(.possibility, .epistemic)} }

/-- The future mode of the verb, expressing circumstantial necessity. -/
def futureMode : ModalItem :=
  { form := "future mode", meaning := {(.necessity, .circumstantial)} }

/-- The potential mode of the verb, expressing circumstantial possibility. -/
def potentialMode : ModalItem :=
  { form := "potential mode", meaning := {(.possibility, .circumstantial)} }

/-- The modal inventory: the expressions with a meaning in positive clauses. -/
def modals : List ModalItem := [gwál, giwe, shákdé, futureMode, potentialMode]

end Tlingit
