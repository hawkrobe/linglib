import Linglib.Syntax.Category.Determiner.ModalIndefinite

/-!
# German modal indefinites

Lexical entry for *irgendein*, the prototypical domain-widening indefinite
([kratzer-shimoyama-2002]).
-/

namespace German.ModalIndefinites

/-- *irgendein*: epistemic or random choice, not upper-bounded, with an unremarkable reading
in predicative position; the modal component is an implicature of domain widening
([kratzer-shimoyama-2002]). -/
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
