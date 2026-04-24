import Linglib.Features.ModalIndefinite

/-!
# Italian Modal Indefinite Fragment
@cite{chierchia-2013}

Lexical entry for Italian modal indefinite *un qualsiasi*.

-/

set_option autoImplicit false

namespace Fragments.Italian.ModalIndefinites

open Features.ModalIndefinite


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entry
-- ════════════════════════════════════════════════════

/-- *un qualsiasi*: at-issue, random choice, not upper-bounded.
    Existential FCI; requires a modal licensor
    (@cite{chierchia-2013}, §5.3.2). -/
def unQualsiasiEntry : ModalIndefiniteEntry where
  language := "Italian"
  form := "un qualsiasi"
  gloss := "a whichever"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := false
  hasUnremarkableReading := false
  canBePredicate := false
  anchorConstraint := some .unrestricted
  source := "Chierchia 2013"

/-- The Italian modal indefinite paradigm. -/
def paradigm : List ModalIndefiniteEntry := [unQualsiasiEntry]


end Fragments.Italian.ModalIndefinites
