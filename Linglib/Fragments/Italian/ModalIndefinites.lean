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
  source := "Chierchia 2013"


-- ════════════════════════════════════════════════════
-- § 2. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem unQualsiasi_at_issue : unQualsiasiEntry.status = .atIssue := rfl
theorem unQualsiasi_rc : unQualsiasiEntry.hasCircumstantial = true := by native_decide
theorem unQualsiasi_no_epistemic : unQualsiasiEntry.hasEpistemic = false := by native_decide
theorem unQualsiasi_not_ub : unQualsiasiEntry.upperBounded = false := rfl


end Fragments.Italian.ModalIndefinites
