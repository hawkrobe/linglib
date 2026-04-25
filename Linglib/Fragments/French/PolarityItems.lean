import Linglib.Core.Lexical.PolarityItem

/-!
# French Polarity-Sensitive Items
@cite{haspelmath-1997} @cite{zanuttini-1997}

Lexical entries for French polarity-sensitive items (n-word series and
related), typed by the theory-neutral categories from
`Core.Lexical.PolarityItem`. Standard sentential negation lives in the
sibling `Fragments/French/Negation.lean`; this file holds only the
lexical reactives (operator/lexical-reactive split documented in
`Core/Lexical/NegMarker.lean`).

## The French n-word series

French *personne*, *rien*, *jamais*, *plus* originate as ordinary nouns
or adverbs ('person', 'thing', 'ever', 'more') that grammaticalized into
negative polarity items via the Jespersen cycle. In modern French they
co-occur with *ne* (where *ne* is preserved): *Je n'ai vu personne*
'I haven't seen anyone', *Il n'y a plus de pain* 'There's no more bread'.
In *ne*-drop registers, the n-word alone carries the negation:
*J'ai vu personne*.

The bipartite-marker dependency (the "*ne*-clitic requirement" of older
schemas) is encoded here as the `.negation` licensing context — the
syntactic detail that *ne* is the visible licenser when present is
captured in the `notes` field. A future typed model of bipartite
licensing would live in the substrate, not per-Fragment.
-/

namespace Fragments.French.PolarityItems

open Core.Lexical.PolarityItem

/-- *personne* — N-word for human ('nobody').
    Grammaticalized from the noun 'person'. Co-occurs with *ne* in
    formal French; stands alone in colloquial *ne*-drop registers. -/
def personne : PolarityItemEntry :=
  { form := "personne"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause, .question]
  , scalarDirection := .strengthening
  , notes :=
      "N-word from 'person'; *Je n'ai vu personne*; co-occurs with " ++
      "*ne* in formal register, stands alone in colloquial *ne*-drop" }

/-- *rien* — N-word for non-human ('nothing').
    Grammaticalized from a Latin noun 'thing'. Same distribution as
    *personne*. -/
def rien : PolarityItemEntry :=
  { form := "rien"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause, .question]
  , scalarDirection := .strengthening
  , notes :=
      "N-word from 'thing'; *Je n'ai rien vu*; same distribution as " ++
      "*personne*" }

/-- *jamais* — Temporal n-word ('never').
    Grammaticalized from 'ever'. Pre-Jespersen *jamais* was a positive
    indefinite; modern *jamais* is the negative, requiring *ne*-licensing
    in formal register. -/
def jamais : PolarityItemEntry :=
  { form := "jamais"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause, .question]
  , scalarDirection := .strengthening
  , notes :=
      "Temporal n-word from 'ever'; *Je n'irai jamais*; Jespersen " ++
      "shift from positive to negative" }

/-- *plus* — Temporal/quantitative n-word ('no more', 'no longer').
    Same lexeme as positive *plus* 'more'; the negative reading requires
    co-occurrence with *ne* (or *ne*-drop register) and contextual
    triggering. -/
def plus : PolarityItemEntry :=
  { form := "plus"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , notes :=
      "N-word 'no more' / 'no longer'; *Il n'y a plus de pain*; " ++
      "homophonous with positive *plus* 'more'" }

-- ============================================================================
-- Joint
-- ============================================================================

/-- The French polarity-item inventory: the Fragment-side joint consumed
    by `Phenomena/Polarity/Typology.lean`. -/
def items : List PolarityItemEntry :=
  [personne, rien, jamais, plus]

-- ============================================================================
-- Verification
-- ============================================================================

/-- All French n-words are weak NPIs licensed by negation. -/
theorem all_npis_licensed_by_negation :
    items.all (fun e => e.licensingContexts.contains .negation) = true := by
  native_decide

end Fragments.French.PolarityItems
