import Linglib.Semantics.Polarity.Item

/-!
# Tagalog Polarity-Sensitive Items
[haspelmath-1997]

Tagalog indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

- **sinuman**: Weak NPI (wh-based, questions/conditionals/indirect neg)
- **walang (tao)**: Negative existential (direct negation)
- **kahit sino**: FCI (concessive + wh: anyone at all)

-/

namespace Tagalog.PolarityItems

open Semantics.Polarity

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *sinuman* — Weak NPI.
    Wh-based polarity-sensitive indefinite. -/
def sinuman : PolarityItemEntry :=
  { form := "sinuman"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation]
  , notes := "wh-based polarity-sensitive indefinite" }

/-- *walang (tao)* — Negative existential.
    'walang dumating' (nobody came). -/
def walang : PolarityItemEntry :=
  { form := "walang (tao)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
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
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "Concessive + wh: anyone at all (FC)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem sinuman_walang_distinct :
    sinuman.form ≠ walang.form := by decide

end Tagalog.PolarityItems
