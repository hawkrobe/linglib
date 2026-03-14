import Linglib.Fragments.English.PolarityItems

/-!
# Russian Polarity-Sensitive Items
@cite{haspelmath-1997}

Russian indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **кто-либо** (kto-libo): Weak NPI (questions, conditionals, indirect negation)
- **никто** (nikto): N-word, negative concord
- **кто угодно** (kto ugodno): Free choice item
-/

namespace Fragments.Russian.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *кто-либо* (kto-libo) — Weak NPI.
    Polarity-sensitive indefinite licensed in questions, conditionals,
    and indirect negation scope. -/
def ktoLibo : PolarityItemEntry :=
  { form := "кто-либо (kto-libo)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditional_ant, .negation]
  , scalarDirection := .strengthening
  , notes := "Polarity-sensitive indefinite" }

/-- *никто* (nikto) — N-word, negative concord.
    Requires clause-level negation: 'nikto ne prišël' (nobody NEG came). -/
def nikto : PolarityItemEntry :=
  { form := "никто (nikto)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .without_clause]
  , scalarDirection := .strengthening
  , notes := "N-word; negative concord: 'nikto ne prišël'" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *кто угодно* (kto ugodno) — Free choice item.
    Universal-like: 'anyone at all'. -/
def ktoUgodno : PolarityItemEntry :=
  { form := "кто угодно (kto ugodno)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Free choice: 'kto ugodno možet èto sdelat'' (anyone can do that)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem nikto_ktoUgodno_distinct :
    nikto.polarityType ≠ ktoUgodno.polarityType := by decide

theorem russian_npis_strengthening :
    [ktoLibo, nikto].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

theorem russian_fci_obligatory_domain_alts :
    ktoUgodno.obligatoryDomainAlts = true := rfl

end Fragments.Russian.PolarityItems
