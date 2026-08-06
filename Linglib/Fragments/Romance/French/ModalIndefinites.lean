import Linglib.Features.ModalIndefinite

/-!
# French Modal Indefinite Fragment

Lexical entry for French modal indefinite *n'importe quel*
([jayez-tovena-2006]).
-/

namespace French.ModalIndefinites

open Features.ModalIndefinite

/-- *n'importe quel*: at-issue, random choice only, not upper-bounded.
    Literally "no matter which"; conveys indiscriminacy
    ([jayez-tovena-2006]). -/
def nimporteQuelEntry : ModalIndefiniteEntry where
  form := "n'importe quel"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted

/-- The French modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [nimporteQuelEntry]

end French.ModalIndefinites
