import Linglib.Fragments.English.PolarityItems

/-!
# Hungarian Polarity-Sensitive Items
@cite{haspelmath-1997}

Hungarian indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **senki**: N-word, negative concord (with *sem* in direct negation)
- **akárki / bárki**: Free choice items
-/

namespace Fragments.Hungarian.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *senki* — N-word, negative concord.
    Covers conditional, indirect negation, and direct negation.
    In direct negation, appears with *sem*: 'senki sem jött' (nobody came). -/
def senki : PolarityItemEntry :=
  { form := "senki"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.conditional_ant, .negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "N-word; with sem in direct neg: 'senki sem jött'" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *akárki / bárki* — Free choice items.
    'Anyone at all': 'akárki megteheti' (anyone can do it). -/
def akarki : PolarityItemEntry :=
  { form := "akárki / bárki"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , notes := "Free choice: anyone at all" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem senki_akarki_distinct :
    senki.polarityType ≠ akarki.polarityType := by decide

end Fragments.Hungarian.PolarityItems
