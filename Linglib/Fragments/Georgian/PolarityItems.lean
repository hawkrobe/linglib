import Linglib.Fragments.English.PolarityItems

/-!
# Georgian Polarity-Sensitive Items
@cite{haspelmath-1997}

Georgian indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **aravin** (არავინ): Negative indefinite (ara- NEG prefix + vin 'who')
- **nebismieri** (ნებისმიერი): Free choice item

Forms and basic distribution verified against @cite{borise-2019} Ch. 4 §2:
aravin is morphologically NEG + wh (not NEG + indefinite), and Georgian is a
non-strict negative concord language (verbal negation *ar* is optional with
preverbal neg-words). Mood-conditioned variants: vera-vin (modal), nura-vin
(prohibitive). nebismieri confirmed as FC indefinite in questions/modals.

-/

namespace Fragments.Georgian.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *aravin* (არავინ) — Negative indefinite.
    Morphologically ara- (NEG) + vin (who): 'aravin (ar) mosula' (nobody came).
    Non-strict negative concord: verbal negation *ar* is optional. -/
def aravin : PolarityItemEntry :=
  { form := "aravin (არავინ)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , notes := "Negative indefinite: ara- (NEG) + vin (who); non-strict NC" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *nebismieri* (ნებისმიერი) — Free choice item.
    'Any / whichever': 'nebismier matarebels' (any train). -/
def nebismieri : PolarityItemEntry :=
  { form := "nebismieri (ნებისმიერი)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , notes := "Free choice: any/every" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem aravin_nebismieri_distinct :
    aravin.polarityType ≠ nebismieri.polarityType := by decide

end Fragments.Georgian.PolarityItems
