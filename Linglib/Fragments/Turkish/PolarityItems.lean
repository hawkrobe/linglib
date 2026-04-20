import Linglib.Core.Lexical.PolarityItem

/-!
# Turkish Polarity-Sensitive Items
@cite{haspelmath-1997}

Turkish indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

- **kimse**: Weak NPI (questions, conditionals, indirect negation)
- **hiç kimse**: Emphatic negative indefinite (direct negation)
- **herhangi biri**: Free choice item
-/

namespace Fragments.Turkish.PolarityItems

open Core.Lexical.PolarityItem

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
  , licensingContexts := [.question, .conditionalAntecedent, .negation]
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
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "Free choice: 'herhangi biri yapabilir' (anyone can do it)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem turkish_npis_strengthening :
    [kimse, hicKimse].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

end Fragments.Turkish.PolarityItems
