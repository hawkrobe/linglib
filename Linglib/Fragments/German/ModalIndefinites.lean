module

public import Linglib.Syntax.Category.Determiner.ModalIndefinite

/-!
# German modal indefinites

This file defines the German modal indefinite *irgendein* 'some … or other'. Its modal component
is epistemic, that the speaker does not know which, or random choice, that any choice would have
done, and it does not survive under a downward-entailing operator such as *nie* 'never' unless
*irgendein* is stressed, so Kratzer and Shimoyama take it to be an implicature of domain
widening. In predicative position it has an unremarkable reading, *Hans ist (nur) irgendein
Student* 'Hans is just some student'. Alonso-Ovalle and Royer compare it with the Chuj and
Romance modal indefinites.

## TODO

The entry's `upperBounded := false` has no source. Alonso-Ovalle and Royer set the Chuj
*yalnhej* apart from other modal indefinites as lacking an upper bound, illustrated by Spanish
*algún* and *uno cualquiera*, and tie the upper bound to singular number marking, which
*irgendein* carries.

## References

* [kratzer-shimoyama-2002]
* [alonso-ovalle-royer-2024]
-/

@[expose] public section

namespace German.ModalIndefinites

/-- *Irgendein* conveys epistemic or random-choice modality as an implicature, and has an
unremarkable reading in predicative position. -/
def irgendein : ModalIndefinite where
  form := "irgendein"
  status := .implicature
  flavors := {.epistemic, .circumstantial}
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true

/-- The German modal indefinite paradigm. -/
def paradigm : List ModalIndefinite := [irgendein]

end German.ModalIndefinites
