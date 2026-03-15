import Linglib.Core.Lexical.PolarityItem

/-!
# Mandarin Polarity-Sensitive Items
@cite{haspelmath-1997}

Mandarin indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

Mandarin wh-words (*shéi* 谁, *shénme* 什么) double as indefinites in
non-interrogative uses, covering an exceptionally wide range on
@cite{haspelmath-1997}'s map (7 of 9 functions):
- **shéi** (non-interrogative): NPI/FCI — questions through free choice
-/

namespace Fragments.Mandarin.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- NPI/FCI
-- ============================================================================

/-- *shéi* (谁, non-interrogative) — NPI/FCI.
    Wh-word as indefinite covers 7 Haspelmath functions: irrealis through
    free choice. Functions as both NPI (under negation, in questions) and
    FCI (in modal/generic contexts). -/
def shei : PolarityItemEntry :=
  { form := "shéi (谁, non-interrog.)"
  , polarityType := .npi_fci
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody, .question, .conditional_ant
      , .modal_possibility, .modal_necessity, .imperative, .generic
      , .comparative ]
  , scalarDirection := .strengthening
  , notes := "Wh-word covers 7 functions: irrealis through free choice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem shei_is_npi_fci : shei.polarityType = .npi_fci := rfl

end Fragments.Mandarin.PolarityItems
