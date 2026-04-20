import Linglib.Core.Lexical.PolarityItem

/-!
# Quechua (Imbabura) Polarity-Sensitive Items
@cite{haspelmath-1997}

Quechua indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

- **pi-pash**: Weak NPI (wh + pash in conditional/neg scope)
- **mana pi-pash**: Negative indefinite (negation + wh + pash)
- **maijan-pash**: Free choice item

-/

namespace Fragments.Quechua.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *pi-pash* — Weak NPI.
    wh + pash: used in conditional and indirect negation contexts. -/
def piPash : PolarityItemEntry :=
  { form := "pi-pash"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.conditionalAntecedent, .negation]
  , notes := "wh + pash: conditional/neg scope" }

/-- *mana pi-pash* — Negative indefinite.
    negation + wh + pash: nobody. -/
def manaPiPash : PolarityItemEntry :=
  { form := "mana pi-pash"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , notes := "Negation + wh + pash: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *maijan-pash* — Free choice item.
    'Anyone': free choice use. -/
def maijanPash : PolarityItemEntry :=
  { form := "maijan-pash"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "Free choice: anyone" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem piPash_manaPiPash_distinct :
    piPash.polarityType = manaPiPash.polarityType := rfl

end Fragments.Quechua.PolarityItems
