import Linglib.Core.Modality.ModalIndefinite

/-!
# Italian Modal Indefinite Fragment
@cite{chierchia-2013}

Lexical entry for Italian modal indefinite *un qualsiasi*.

-/

namespace Fragments.Italian.ModalIndefinites

open Core.ModalIndefinite
open Core.Modality (ModalFlavor)


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


-- ════════════════════════════════════════════════════
-- § 2. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem unQualsiasi_at_issue : unQualsiasiEntry.status = .atIssue := rfl
theorem unQualsiasi_rc : unQualsiasiEntry.hasCircumstantial = true := rfl
theorem unQualsiasi_no_epistemic : unQualsiasiEntry.hasEpistemic = false := rfl
theorem unQualsiasi_not_ub : unQualsiasiEntry.upperBounded = false := rfl
theorem unQualsiasi_unrestricted : unQualsiasiEntry.anchorConstraint = some .unrestricted := rfl


end Fragments.Italian.ModalIndefinites
