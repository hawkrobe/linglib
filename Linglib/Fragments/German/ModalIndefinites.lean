import Linglib.Features.ModalIndefinite

/-!
# German Modal Indefinite Fragment
[kratzer-shimoyama-2002]

Lexical entry for German modal indefinite *irgendein*, the prototypical
domain-widening indefinite ([kratzer-shimoyama-2002]).

-/

set_option autoImplicit false

namespace German.ModalIndefinites

open Features.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entry
-- ════════════════════════════════════════════════════

/-- *irgendein*: not-at-issue, epistemic + random choice, not upper-bounded.
    Epistemic in episodic assertions; free choice under deontic modals.
    Domain widening is the core mechanism
    ([kratzer-shimoyama-2002]). -/
def irgendeinEntry : ModalIndefiniteEntry where
  language := "German"
  form := "irgendein"
  gloss := "IRGEND.one"
  status := .notAtIssue
  flavors := [.epistemic, .circumstantial]
  upperBounded := false
  hasUnremarkableReading := true
  canBePredicate := true
  source := "Kratzer & Shimoyama 2002"

/-- The German modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [irgendeinEntry]


end German.ModalIndefinites
