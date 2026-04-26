import Linglib.Core.Lexical.PolarityItem

/-!
# Czech Polarity-Sensitive Items
@cite{haspelmath-1997}

Lexical entries for Czech n-words (the *ni-* series), typed by the
theory-neutral categories from `Core.Lexical.PolarityItem`. Standard
sentential negation (the *ne-* prefix) lives in the sibling
`Fragments/Czech/Negation.lean`; this file holds only the lexical
reactives (operator/lexical-reactive split documented in
`Core/Lexical/NegMarker.lean`).

## The Czech *ni-* series

Czech is a strict-NC language (Slavic pattern): every n-word obligatorily
co-occurs with the *ne-* prefixed verb form, regardless of position.
*Nikdo nepřišel* 'Nobody NEG.came'; *Neviděl nikoho* 'NEG.saw nobody'.
Both preverbal and postverbal n-words require *ne-* — unlike Italian/
Spanish position-dependent NC.
-/

namespace Fragments.Slavic.Czech.PolarityItems

open Core.Lexical.PolarityItem

/-- *nikdo* — N-word for human ('nobody').
    Strict NC: requires the *ne-* prefix on the verb regardless of
    position. -/
def nikdo : PolarityItemEntry :=
  { form := "nikdo"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , notes := "Strict-NC n-word; *Nikdo nepřišel* / *Neviděl nikoho*" }

/-- *nic* — N-word for non-human ('nothing'). -/
def nic : PolarityItemEntry :=
  { form := "nic"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , notes := "Non-human n-word; *Nic neviděl*" }

/-- *nikdy* — Temporal n-word ('never'). -/
def nikdy : PolarityItemEntry :=
  { form := "nikdy"
  , polarityType := .npiStrong
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , notes := "Temporal n-word; *Nikdy nepřišel*" }

/-- *nikam* — Locative n-word ('nowhere'). -/
def nikam : PolarityItemEntry :=
  { form := "nikam"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , notes := "Locative directional n-word; *Nikam nejde* 'goes nowhere'" }

/-- *žádný* — Determiner n-word ('no/none'). -/
def zadny : PolarityItemEntry :=
  { form := "žádný"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes :=
      "Determiner/pronoun n-word ('no/none'); morphologically distinct " ++
      "from the *ni-* series but functionally parallel" }

-- ============================================================================
-- Joint
-- ============================================================================

/-- The Czech polarity-item inventory: the Fragment-side joint consumed
    by `Phenomena/Polarity/Typology.lean`. -/
def items : List PolarityItemEntry :=
  [nikdo, nic, nikdy, nikam, zadny]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Czech n-words are licensed by negation. -/
theorem all_npis_licensed_by_negation :
    items.all (fun e => e.licensingContexts.contains .negation) = true := by
  native_decide

/-- The *ni-* series is morphologically marked as `indefPlusNeg`. -/
theorem niSeries_morphology :
    [nikdo, nic, nikdy, nikam].all (fun e => e.morphology == .indefPlusNeg) = true := by
  native_decide

end Fragments.Slavic.Czech.PolarityItems
