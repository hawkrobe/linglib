import Linglib.Syntax.Category.Determiner.ModalIndefinite

/-!
# Italian modal indefinites

Lexical entry for *un qualsiasi* ([chierchia-2013]).
-/

namespace Italian.ModalIndefinites

/-- *un qualsiasi*: at-issue random choice, not upper-bounded; an existential free choice
item requiring a modal licensor ([chierchia-2013], §5.3.2). -/
def unQualsiasi : ModalIndefinite where
  form := "un qualsiasi"
  status := .atIssue
  flavors := {.circumstantial}
  upperBounded := false
  anchorConstraint := some .unrestricted

/-- The Italian modal indefinite paradigm. -/
def paradigm : List ModalIndefinite := [unQualsiasi]

end Italian.ModalIndefinites
