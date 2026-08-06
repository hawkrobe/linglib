import Linglib.Features.ModalIndefinite

/-!
# German Modal Indefinite Fragment

Lexical entry for German modal indefinite *irgendein*, the prototypical
domain-widening indefinite ([kratzer-shimoyama-2002]).
-/

namespace German.ModalIndefinites

open Features.ModalIndefinite

/-- *irgendein*: not-at-issue, epistemic + random choice, not
    upper-bounded. Epistemic in episodic assertions; free choice under
    deontic modals. Domain widening is the core mechanism
    ([kratzer-shimoyama-2002]). -/
def irgendeinEntry : ModalIndefiniteEntry where
  form := "irgendein"
  status := .notAtIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true

/-- The German modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [irgendeinEntry]

end German.ModalIndefinites
