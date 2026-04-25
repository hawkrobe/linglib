import Linglib.Core.Lexical.PolarityItem

/-!
# Spanish Polarity-Sensitive Items
@cite{haspelmath-1997} @cite{zanuttini-1997}

Lexical entries for Spanish polarity-sensitive items (n-word series),
typed by the theory-neutral categories from `Core.Lexical.PolarityItem`.
Standard sentential negation (the *no* marker) lives in the sibling
`Fragments/Spanish/Negation.lean`; this file holds only the lexical
reactives (operator/lexical-reactive split documented in
`Core/Lexical/NegMarker.lean`).

## The Spanish n-word series

Spanish has position-dependent NC: preverbal n-words preclude *no*
(*Nadie vino* 'Nobody came'); postverbal n-words require *no*
(*No vi nada* 'I didn't see anything'). The pattern parallels Italian.
The position-dependent `.negation` licensing is encoded uniformly here
via `licensingContexts := [.negation, ...]` — the position-dependence
is a syntactic fact about the marker–n-word interaction, not a
lexical-feature distinction across n-words.
-/

namespace Fragments.Spanish.PolarityItems

open Core.Lexical.PolarityItem

/-- *nadie* — N-word for human ('nobody').
    Preverbal alone: *Nadie vino*. Postverbal with *no*: *No vino nadie*. -/
def nadie : PolarityItemEntry :=
  { form := "nadie"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "N-word; co-occurs with *no* postverbally, alone preverbally" }

/-- *nada* — N-word for non-human ('nothing'). Same distribution as *nadie*. -/
def nada : PolarityItemEntry :=
  { form := "nada"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "Non-human N-word; *No vi nada* / *Nada vi*" }

/-- *nunca* — Temporal N-word ('never'). -/
def nunca : PolarityItemEntry :=
  { form := "nunca"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "Temporal N-word; *Nunca viene* / *No viene nunca*" }

/-- *ninguno* — N-word adjective/pronoun ('none / no'). -/
def ninguno : PolarityItemEntry :=
  { form := "ninguno"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "N-word adjective/pronoun; *Ninguno vino* / *No vi a ninguno*" }

/-- *jamás* — Temporal N-word ('never', emphatic register).
    Functional variant of *nunca*; both can co-occur (*nunca jamás*) for
    superlative emphasis. -/
def jamas : PolarityItemEntry :=
  { form := "jamás"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "Emphatic temporal N-word; cf. *nunca* (more frequent)" }

-- ============================================================================
-- Joint
-- ============================================================================

/-- The Spanish polarity-item inventory: the Fragment-side joint consumed
    by `Phenomena/Polarity/Typology.lean`. -/
def items : List PolarityItemEntry :=
  [nadie, nada, nunca, ninguno, jamas]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Spanish n-words are weak NPIs licensed by negation. -/
theorem all_npis_licensed_by_negation :
    items.all (fun e => e.licensingContexts.contains .negation) = true := by
  native_decide

end Fragments.Spanish.PolarityItems
