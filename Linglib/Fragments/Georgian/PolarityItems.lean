import Linglib.Fragments.English.PolarityItems

/-!
# Georgian Polarity-Sensitive Items
@cite{haspelmath-1997}

Georgian indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **aravin** (არავინ): Negative indefinite (NEG + vinme)
- **nebismieri** (ნებისმიერი): Free choice item

Properties beyond the @cite{haspelmath-1997} function data (scalar direction,
domain alternatives, modal rescue) use conservative defaults. -- UNVERIFIED
-/

namespace Fragments.Georgian.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *aravin* (არავინ) — Negative indefinite.
    Morphologically NEG + vinme: 'aravin ar mosula' (nobody came). -/
def aravin : PolarityItemEntry :=
  { form := "aravin (არავინ)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening  -- UNVERIFIED: conservative default
  , notes := "Negative indefinite: NEG + vinme" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *nebismieri* (ნებისმიერი) — Free choice item.
    'Any / every': 'nebismieri adamiani' (any person). -/
def nebismieri : PolarityItemEntry :=
  { form := "nebismieri (ნებისმიერი)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true  -- UNVERIFIED: conservative default
  , modalRescue := true  -- UNVERIFIED: conservative default
  , notes := "Free choice: any/every" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem aravin_nebismieri_distinct :
    aravin.polarityType ≠ nebismieri.polarityType := by decide

end Fragments.Georgian.PolarityItems
