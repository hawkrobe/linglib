import Linglib.Core.Lexical.PolarityItem

/-!
# Russian Polarity-Sensitive Items
@cite{haspelmath-1997}

Russian indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

- **кто-либо** (kto-libo): Weak NPI (questions, conditionals, indirect negation)
- **никто** (nikto): N-word, negative concord
- **кто угодно** (kto ugodno): Free choice item
-/

namespace Fragments.Slavic.Russian.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *кто-либо* (kto-libo) — Weak NPI.
    Polarity-sensitive indefinite licensed in questions, conditionals,
    and indirect negation scope. -/
def ktoLibo : PolarityItemEntry :=
  { form := "кто-либо (kto-libo)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation]
  , scalarDirection := .strengthening
  , notes := "Polarity-sensitive indefinite" }

/-- *никто* (nikto) — N-word, negative concord.
    Requires clause-level negation: 'nikto ne prišël' (nobody NEG came). -/
def nikto : PolarityItemEntry :=
  { form := "никто (nikto)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "N-word; negative concord: 'nikto ne prišël'" }

/-- *ничего* (nichego) — Non-human N-word; obligatory negative concord.
    'Ničego ne videl' (NEG saw nothing) = "(I) saw nothing". -/
def nichego : PolarityItemEntry :=
  { form := "ничего (nichego)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "Non-human N-word; genitive form ничего; co-occurs with не" }

/-- *никогда* (nikogda) — Temporal N-word; obligatory negative concord.
    'Nikogda ne prixodil' (never NEG came) = "(He) never came". -/
def nikogda : PolarityItemEntry :=
  { form := "никогда (nikogda)"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "Temporal N-word; co-occurs with не" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *кто угодно* (kto ugodno) — Free choice item.
    Universal-like: 'anyone at all'. -/
def ktoUgodno : PolarityItemEntry :=
  { form := "кто угодно (kto ugodno)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "Free choice: 'kto ugodno možet èto sdelat'' (anyone can do that)" }

-- ============================================================================
-- Joint
-- ============================================================================

/-- The Russian polarity-item inventory: the Fragment-side joint consumed
    by `Phenomena/Polarity/Typology.lean`. -/
def items : List PolarityItemEntry :=
  [ktoLibo, nikto, nichego, nikogda, ktoUgodno]

-- ============================================================================
-- Verification
-- ============================================================================

theorem nikto_ktoUgodno_distinct :
    nikto.polarityType ≠ ktoUgodno.polarityType := by decide

theorem russian_npis_strengthening :
    [ktoLibo, nikto, nichego, nikogda].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

end Fragments.Slavic.Russian.PolarityItems
