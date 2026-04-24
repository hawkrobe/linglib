import Linglib.Features.ModalIndefinite

/-!
# French Modal Indefinite Fragment
@cite{jayez-tovena-2006}

Lexical entry for French modal indefinite *n'importe quel*.

-/

set_option autoImplicit false

namespace Fragments.French.ModalIndefinites

open Features.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entry
-- ════════════════════════════════════════════════════

/-- *n'importe quel*: at-issue, random choice only, not upper-bounded.
    Literally "no matter which"; conveys indiscriminacy
    (@cite{jayez-tovena-2006}). -/
def nimporteQuelEntry : ModalIndefiniteEntry where
  language := "French"
  form := "n'importe quel"
  gloss := "no matter which"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted
  source := "Jayez & Tovena 2006"

/-- The French modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [nimporteQuelEntry]


end Fragments.French.ModalIndefinites
