import Linglib.Core.Modality.ModalIndefinite

/-!
# German Modal Indefinite Fragment
@cite{kratzer-shimoyama-2002}

Lexical entry for German modal indefinite *irgendein*, the prototypical
domain-widening indefinite (@cite{kratzer-shimoyama-2002}).

-/

namespace Fragments.German.ModalIndefinites

open Core.ModalIndefinite
open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entry
-- ════════════════════════════════════════════════════

/-- *irgendein*: not-at-issue, epistemic + random choice, not upper-bounded.
    Epistemic in episodic assertions; free choice under deontic modals.
    Domain widening is the core mechanism
    (@cite{kratzer-shimoyama-2002}). -/
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


-- ════════════════════════════════════════════════════
-- § 2. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem irgendein_not_at_issue : irgendeinEntry.status = .notAtIssue := rfl
theorem irgendein_has_epistemic : irgendeinEntry.hasEpistemic = true := by native_decide
theorem irgendein_has_rc : irgendeinEntry.hasCircumstantial = true := by native_decide
theorem irgendein_not_ub : irgendeinEntry.upperBounded = false := rfl
theorem irgendein_has_unremarkable : irgendeinEntry.hasUnremarkableReading = true := rfl


end Fragments.German.ModalIndefinites
