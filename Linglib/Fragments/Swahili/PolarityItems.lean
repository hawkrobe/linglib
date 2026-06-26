import Linglib.Semantics.Polarity.Item

/-!
# Swahili Polarity-Sensitive Items
[haspelmath-1997]

Swahili indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

- **hakuna mtu / mtu …-si-**: Negative indefinite
- **mtu ye yote**: FCI ('person any whatsoever')

-/

namespace Swahili.PolarityItems

open Semantics.Polarity

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

end Swahili.PolarityItems
