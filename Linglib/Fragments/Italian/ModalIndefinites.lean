import Linglib.Features.ModalIndefinite

/-!
# Italian Modal Indefinite Fragment

Lexical entry for Italian modal indefinite *un qualsiasi*
([chierchia-2013]).
-/

namespace Italian.ModalIndefinites

open Features.ModalIndefinite

/-- *un qualsiasi*: at-issue, random choice, not upper-bounded.
    Existential FCI; requires a modal licensor
    ([chierchia-2013], §5.3.2). -/
def unQualsiasiEntry : ModalIndefiniteEntry where
  form := "un qualsiasi"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted

/-- The Italian modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [unQualsiasiEntry]

end Italian.ModalIndefinites
