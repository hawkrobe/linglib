import Linglib.Fragments.English.PolarityItems

/-!
# Swahili Polarity-Sensitive Items
@cite{haspelmath-1997}

Swahili indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **hakuna mtu / mtu …-si-**: Negative indefinite
- **mtu ye yote**: FCI ('person any whatsoever')

Properties beyond the @cite{haspelmath-1997} function data (scalar direction,
domain alternatives, modal rescue) use conservative defaults. -- UNVERIFIED
-/

namespace Fragments.Swahili.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *hakuna mtu / mtu …-si-* — Negative indefinite.
    Negative existential or negative verb concord: nobody. -/
def hakunaMtu : PolarityItemEntry :=
  { form := "hakuna mtu"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening  -- UNVERIFIED: conservative default
  , notes := "Negative existential or negative verb concord: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *mtu ye yote* — Free choice item.
    'Person any whatsoever': free choice. -/
def mtuYeYote : PolarityItemEntry :=
  { form := "mtu ye yote"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true  -- UNVERIFIED: conservative default
  , modalRescue := true  -- UNVERIFIED: conservative default
  , notes := "Person any whatsoever: free choice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem hakunaMtu_mtuYeYote_distinct :
    hakunaMtu.polarityType ≠ mtuYeYote.polarityType := by decide

end Fragments.Swahili.PolarityItems
