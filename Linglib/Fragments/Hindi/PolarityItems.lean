import Linglib.Core.Lexical.PolarityItem

/-!
# Hindi Polarity-Sensitive Items
@cite{haspelmath-1997}

Hindi indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

Hindi builds polarity items from the general indefinite *koii* + particles:
- **koii nahiiN**: koii + negation → NPI (nobody)
- **koii bhii**: koii + bhii (even/also) → FCI (anyone at all)
-/

namespace Fragments.Hindi.PolarityItems

open Core.Lexical.PolarityItem

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
  , morphology := .indefPlusNeg
  , alternativeType := .contextualProperty
  , notes := "koii + negation: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *koii bhii* — Free choice item.
    koii + bhii (even/also): 'koii bhii yah kar saktaa hai'
    (anyone can do this). @cite{lahiri-1998} -/
def koiiBhii : PolarityItemEntry :=
  { form := "koii bhii"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , morphology := .indefPlusEven
  , alternativeType := .contextualProperty
  , notes := "koii + bhii (even/also): anyone at all (FC)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem koiiNahiin_koiiBhii_distinct :
    koiiNahiin.polarityType ≠ koiiBhii.polarityType := by decide

end Fragments.Hindi.PolarityItems
