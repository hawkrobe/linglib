import Linglib.Semantics.Polarity.Item

/-!
# Spanish Polarity-Sensitive Items
[haspelmath-1997] [zanuttini-1997]

Lexical entries for Spanish polarity-sensitive items (n-word series),
typed by the theory-neutral categories from `Semantics.Polarity`.
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

namespace Spanish.PolarityItems

open Semantics.Polarity

/-- *nadie* — N-word for human ('nobody').
    Preverbal alone: *Nadie vino*. Postverbal with *no*: *No vino nadie*. -/
def nadie : Item :=
  { form := "nadie"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *nada* — N-word for non-human ('nothing'). Same distribution as *nadie*. -/
def nada : Item :=
  { form := "nada"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *nunca* — Temporal N-word ('never'). -/
def nunca : Item :=
  { form := "nunca"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *ninguno* — N-word adjective/pronoun ('none / no'). -/
def ninguno : Item :=
  { form := "ninguno"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *jamás* — Temporal N-word ('never', emphatic register).
    Functional variant of *nunca*; both can co-occur (*nunca jamás*) for
    superlative emphasis. -/
def jamas : Item :=
  { form := "jamás"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

-- ============================================================================
-- Joint
-- ============================================================================

/-- The Spanish polarity-item inventory: the Fragment-side joint listing
    every polarity item this fragment defines. -/
def items : List Item :=
  [nadie, nada, nunca, ninguno, jamas]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All Spanish n-words are weak NPIs licensed by negation. -/
theorem all_npis_licensed_by_negation :
    items.all (fun e => e.licensingContexts.contains .negation) = true := by
  decide

end Spanish.PolarityItems
