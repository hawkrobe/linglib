import Linglib.Fragments.English.PolarityItems

/-!
# Tagalog Polarity-Sensitive Items
@cite{haspelmath-1997}

Tagalog indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **sinuman**: Weak NPI (wh-based, questions/conditionals/indirect neg)
- **walang (tao)**: Negative existential (direct negation)
- **kahit sino**: FCI (concessive + wh: anyone at all)

Properties beyond the @cite{haspelmath-1997} function data (scalar direction,
domain alternatives, modal rescue) use conservative defaults. -- UNVERIFIED
-/

namespace Fragments.Tagalog.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *sinuman* — Weak NPI.
    Wh-based polarity-sensitive indefinite. -/
def sinuman : PolarityItemEntry :=
  { form := "sinuman"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditional_ant, .negation]
  , scalarDirection := .strengthening  -- UNVERIFIED: conservative default
  , notes := "wh-based polarity-sensitive indefinite" }

/-- *walang (tao)* — Negative existential.
    'walang dumating' (nobody came). -/
def walang : PolarityItemEntry :=
  { form := "walang (tao)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening  -- UNVERIFIED: conservative default
  , notes := "Negative existential: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *kahit sino* — Free choice item.
    Concessive + wh: 'kahit sino ay pwedeng gawin ito'
    (anyone can do this). -/
def kahitSino : PolarityItemEntry :=
  { form := "kahit sino"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true  -- UNVERIFIED: conservative default
  , modalRescue := true  -- UNVERIFIED: conservative default
  , notes := "Concessive + wh: anyone at all (FC)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem tagalog_npis_strengthening :
    [sinuman, walang].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

theorem kahitSino_obligatory_domain_alts :
    kahitSino.obligatoryDomainAlts = true := rfl

end Fragments.Tagalog.PolarityItems
