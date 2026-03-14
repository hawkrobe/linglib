import Linglib.Fragments.English.PolarityItems

/-!
# Turkish Polarity-Sensitive Items
@cite{haspelmath-1997}

Turkish indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **kimse**: Weak NPI (questions, conditionals, indirect negation)
- **hiç kimse**: Emphatic negative indefinite (direct negation)
- **herhangi biri**: Free choice item
-/

namespace Fragments.Turkish.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *kimse* — Weak NPI.
    Historically 'person'; now polarity-sensitive in questions,
    conditionals, and indirect negation. -/
def kimse : PolarityItemEntry :=
  { form := "kimse"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditional_ant, .negation]
  , scalarDirection := .strengthening
  , notes := "Polarity-sensitive; historically 'person' > NPI" }

/-- *hiç kimse* — Emphatic negative indefinite.
    *hiç* intensifier + *kimse*; direct negation only. -/
def hicKimse : PolarityItemEntry :=
  { form := "hiç kimse"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "hiç intensifier: 'hiç kimse gelmedi' (nobody came)" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *herhangi biri* — Free choice item.
    'Any person at all'. -/
def herhangiBiri : PolarityItemEntry :=
  { form := "herhangi biri"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Free choice: 'herhangi biri yapabilir' (anyone can do it)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem turkish_npis_strengthening :
    [kimse, hicKimse].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

theorem herhangiBiri_obligatory_domain_alts :
    herhangiBiri.obligatoryDomainAlts = true := rfl

end Fragments.Turkish.PolarityItems
