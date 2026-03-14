import Linglib.Fragments.English.PolarityItems

/-!
# Mandarin Polarity-Sensitive Items
@cite{haspelmath-1997}

Mandarin indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

Mandarin wh-words (*shéi* 谁, *shénme* 什么) double as indefinites in
non-interrogative uses, covering an exceptionally wide range on
@cite{haspelmath-1997}'s map (7 of 9 functions):
- **shéi** (non-interrogative): NPI/FCI — questions through free choice
-/

namespace Fragments.Mandarin.PolarityItems

open Fragments.English.PolarityItems

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
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Wh-word covers 7 functions: irrealis through free choice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem shei_is_npi_fci : shei.polarityType = .npi_fci := rfl

theorem shei_obligatory_domain_alts :
    shei.obligatoryDomainAlts = true := rfl

end Fragments.Mandarin.PolarityItems
