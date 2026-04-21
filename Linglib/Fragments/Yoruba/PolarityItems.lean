import Linglib.Core.Lexical.PolarityItem

/-!
# Yoruba Polarity-Sensitive Items
@cite{haspelmath-1997}

Yoruba indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

Yoruba has a minimally differentiated system with a single polarity-sensitive
form covering both NPI and FCI functions:
- **ẹ̀nìkẹ́ni**: NPI/FCI (indirect neg, direct neg, comparative, free choice)

-/

namespace Fragments.Yoruba.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- NPI/FCI
-- ============================================================================

/-- *ẹ̀nìkẹ́ni* — NPI/FCI.
    Covers both negation and free choice functions on Haspelmath's map
    (indirect neg, direct neg, comparative, free choice). -/
def enikeni : PolarityItemEntry :=
  { form := "ẹ̀nìkẹ́ni"
  , polarityType := .npiFci
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody
      , .modalPossibility, .modalNecessity, .imperative, .generic
      , .comparativeNP, .comparativeS ]
  , notes := "Covers 4 Haspelmath functions: indirectNeg through freeChoice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem enikeni_is_npi_fci : enikeni.polarityType = .npiFci := rfl

end Fragments.Yoruba.PolarityItems
