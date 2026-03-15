import Linglib.Core.Modality.ModalIndefinite

/-!
# Spanish Modal Indefinite Fragment
@cite{alonso-ovalle-menendez-benito-2010} @cite{alonso-ovalle-menendez-benito-2018}

Lexical entries for Spanish modal indefinites *algún* and *uno cualquiera*.

- *algún*: epistemic modal indefinite with anti-singleton constraint
  (@cite{alonso-ovalle-menendez-benito-2010}).
- *uno cualquiera*: random choice modal indefinite with anti-singleton
  constraint (@cite{alonso-ovalle-menendez-benito-2018}).

-/

namespace Fragments.Spanish.ModalIndefinites

open Core.ModalIndefinite
open Core.Modality (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Lexical Entries
-- ════════════════════════════════════════════════════

/-- *algún*: not-at-issue, epistemic only, upper-bounded.
    The modal component is a conversational implicature derived from
    the anti-singleton constraint on the domain
    (@cite{alonso-ovalle-menendez-benito-2010}, §4). -/
def algúnEntry : ModalIndefiniteEntry where
  language := "Spanish"
  form := "algún"
  gloss := "ALGÚN"
  status := .notAtIssue
  flavors := [.epistemic]
  upperBounded := true
  hasUnremarkableReading := false
  canBePredicate := false
  source := "Alonso-Ovalle & Menéndez-Benito 2010"

/-- *uno cualquiera*: at-issue, random choice only, upper-bounded.
    The random choice interpretation requires a volitional predicate;
    with non-volitional predicates only the unremarkable reading
    is available (@cite{alonso-ovalle-menendez-benito-2018}, §1.1). -/
def unoCualquieraEntry : ModalIndefiniteEntry where
  language := "Spanish"
  form := "uno cualquiera"
  gloss := "one whichever"
  status := .atIssue
  flavors := [.circumstantial]
  upperBounded := true
  hasUnremarkableReading := true
  canBePredicate := true
  source := "Alonso-Ovalle & Menéndez-Benito 2018"


-- ════════════════════════════════════════════════════
-- § 2. Per-Entry Verification
-- ════════════════════════════════════════════════════

theorem algún_not_at_issue : algúnEntry.status = .notAtIssue := rfl
theorem algún_epistemic : algúnEntry.hasEpistemic = true := by native_decide
theorem algún_no_rc : algúnEntry.hasCircumstantial = false := by native_decide
theorem algún_ub : algúnEntry.upperBounded = true := rfl

theorem unoCualquiera_at_issue : unoCualquieraEntry.status = .atIssue := rfl
theorem unoCualquiera_rc : unoCualquieraEntry.hasCircumstantial = true := by native_decide
theorem unoCualquiera_no_epistemic : unoCualquieraEntry.hasEpistemic = false := by native_decide
theorem unoCualquiera_ub : unoCualquieraEntry.upperBounded = true := rfl

/-- *algún* and *uno cualquiera* share upper-boundedness but differ in
    status and flavor: *algún* is not-at-issue + epistemic, *uno cualquiera*
    is at-issue + random choice. -/
theorem algún_unoCualquiera_contrast :
    algúnEntry.status ≠ unoCualquieraEntry.status ∧
    algúnEntry.flavors ≠ unoCualquieraEntry.flavors ∧
    algúnEntry.upperBounded = unoCualquieraEntry.upperBounded := by
  refine ⟨by decide, by decide, rfl⟩


end Fragments.Spanish.ModalIndefinites
