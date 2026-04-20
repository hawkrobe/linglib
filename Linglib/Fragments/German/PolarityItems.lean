import Linglib.Core.Lexical.PolarityItem

/-!
# German Polarity-Sensitive Items
@cite{haspelmath-1997} @cite{chierchia-2006}

German indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

German's *irgendein* is a key example in @cite{chierchia-2006}'s typology
as an existential FCI with both NPI and FCI uses:
- **irgendein/irgendwer**: NPI/FCI (*irgend-* prefix = domain widening)
- **wer** (conditional): Bare wh-word as weak NPI
- **niemand**: Negative indefinite
-/

namespace Fragments.German.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *irgendein/irgendwer* — NPI/FCI.
    @cite{chierchia-2006}'s EFCI class: existential FCI with both
    NPI uses (questions) and FCI uses (irrealis, modals).
    The *irgend-* prefix marks non-specificity / domain widening. -/
def irgendein : PolarityItemEntry :=
  { form := "irgendein/irgendwer"
  , polarityType := .npiFci
  , baseForce := .existential
  , licensingContexts :=
      [.question, .conditionalAntecedent, .modalPossibility, .modalNecessity, .imperative]
  , scalarDirection := .strengthening
  , notes := "irgend- prefix = domain widening; Chierchia's EFCI class" }

/-- *wer* (conditional/negative) — Bare wh-word as weak NPI.
    Used as indefinite in conditionals and indirect negation contexts. -/
def wer : PolarityItemEntry :=
  { form := "wer (conditional)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.conditionalAntecedent, .negation]
  , scalarDirection := .strengthening
  , notes := "Bare wh-word in conditional/neg contexts" }

/-- *niemand* — Negative indefinite.
    Direct negation; no negative concord (unlike Russian/Italian N-words). -/
def niemand : PolarityItemEntry :=
  { form := "niemand"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "Negative quantifier: 'Niemand kam' (nobody came)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem irgendein_is_npi_fci : irgendein.polarityType = .npiFci := rfl

theorem german_npis_strengthening :
    [irgendein, wer, niemand].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

end Fragments.German.PolarityItems
