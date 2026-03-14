import Linglib.Fragments.English.PolarityItems

/-!
# Hindi Polarity-Sensitive Items
@cite{haspelmath-1997}

Hindi indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

Hindi builds polarity items from the general indefinite *koii* + particles:
- **koii nahiiN**: koii + negation → NPI (nobody)
- **koii bhii**: koii + bhii (even/also) → FCI (anyone at all)
-/

namespace Fragments.Hindi.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *koii nahiiN* — Negative indefinite.
    koii + negation: 'koii nahiiN aayaa' (nobody came). -/
def koiiNahiin : PolarityItemEntry :=
  { form := "koii nahiiN"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "koii + negation: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *koii bhii* — Free choice item.
    koii + bhii (even/also): 'koii bhii yah kar saktaa hai'
    (anyone can do this). -/
def koiiBhii : PolarityItemEntry :=
  { form := "koii bhii"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "koii + bhii (even/also): anyone at all (FC)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem koiiNahiin_koiiBhii_distinct :
    koiiNahiin.polarityType ≠ koiiBhii.polarityType := by decide

theorem koiiBhii_obligatory_domain_alts :
    koiiBhii.obligatoryDomainAlts = true := rfl

end Fragments.Hindi.PolarityItems
