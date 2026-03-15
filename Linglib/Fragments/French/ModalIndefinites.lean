import Linglib.Core.Modality.ModalIndefinite

/-!
# French Modal Indefinite Fragment
@cite{jayez-tovena-2006}

Lexical entry for French modal indefinite *n'importe quel*.

-/

namespace Fragments.French.ModalIndefinites

open Core.ModalIndefinite
open Core.Modality (ModalFlavor)


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
  source := "Jayez & Tovena 2006"


-- ════════════════════════════════════════════════════
-- § 2. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem nimporteQuel_at_issue : nimporteQuelEntry.status = .atIssue := rfl
theorem nimporteQuel_rc : nimporteQuelEntry.hasCircumstantial = true := by native_decide
theorem nimporteQuel_no_epistemic : nimporteQuelEntry.hasEpistemic = false := by native_decide
theorem nimporteQuel_not_ub : nimporteQuelEntry.upperBounded = false := rfl


end Fragments.French.ModalIndefinites
