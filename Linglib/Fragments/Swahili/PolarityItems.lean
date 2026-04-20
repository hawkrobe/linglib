import Linglib.Core.Lexical.PolarityItem

/-!
# Swahili Polarity-Sensitive Items
@cite{haspelmath-1997}

Swahili indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

- **hakuna mtu / mtu …-si-**: Negative indefinite
- **mtu ye yote**: FCI ('person any whatsoever')

-/

namespace Fragments.Swahili.PolarityItems

open Core.Lexical.PolarityItem

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
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "Person any whatsoever: free choice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem hakunaMtu_mtuYeYote_distinct :
    hakunaMtu.polarityType ≠ mtuYeYote.polarityType := by decide

end Fragments.Swahili.PolarityItems
