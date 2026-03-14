import Linglib.Fragments.English.PolarityItems

/-!
# Yoruba Polarity-Sensitive Items
@cite{haspelmath-1997}

Yoruba indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

Yoruba has a minimally differentiated system with a single polarity-sensitive
form covering both NPI and FCI functions:
- **ẹ̀nìkẹ́ni**: NPI/FCI (indirect neg, direct neg, comparative, free choice)

-/

namespace Fragments.Yoruba.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI/FCI
-- ============================================================================

/-- *ẹ̀nìkẹ́ni* — NPI/FCI.
    Covers both negation and free choice functions on Haspelmath's map
    (indirect neg, direct neg, comparative, free choice). -/
def enikeni : PolarityItemEntry :=
  { form := "ẹ̀nìkẹ́ni"
  , polarityType := .npi_fci
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody
      , .modal_possibility, .modal_necessity, .imperative, .generic
      , .comparative ]
  , notes := "Covers 4 Haspelmath functions: indirectNeg through freeChoice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem enikeni_is_npi_fci : enikeni.polarityType = .npi_fci := rfl

end Fragments.Yoruba.PolarityItems
