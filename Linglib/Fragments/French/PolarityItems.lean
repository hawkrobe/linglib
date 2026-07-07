import Linglib.Semantics.Polarity.Licensing

/-!
# French Polarity-Sensitive Items
[haspelmath-1997] [zanuttini-1997]

Lexical entries for French polarity-sensitive items (n-word series and
related), typed by the theory-neutral categories from
`Semantics.Polarity`. Standard sentential negation lives in the
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

French negative concord is non-strict (n-words license each other and
*ne* is droppable), so *personne*/*rien* carry
`licensor := some .antiAdditive` — concord under a negative quantifier is
anti-additive licensing at this grain — while *jamais* keeps the weak-NPI
distribution of its ever face (questions). A typed model of the
bipartite *ne* dependency would live in the substrate, not per-Fragment.
-/

namespace French.PolarityItems

open Semantics.Polarity

/-- *personne* — N-word for human ('nobody').
    Grammaticalized from the noun 'person'. Co-occurs with *ne* in
    formal French; stands alone in colloquial *ne*-drop registers. -/
def personne : Item :=
  { form := "personne"
  , licensor := some .antiAdditive
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *rien* — N-word for non-human ('nothing').
    Grammaticalized from a Latin noun 'thing'. Same distribution as
    *personne*. -/
def rien : Item :=
  { form := "rien"
  , licensor := some .antiAdditive
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening }

/-- *jamais* — Temporal n-word ('never').
    Grammaticalized from 'ever'. Pre-Jespersen *jamais* was a positive
    indefinite; modern *jamais* is the negative, requiring *ne*-licensing
    in formal register. -/
def jamais : Item :=
  { form := "jamais"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause, .question]
  , scalarDirection := .strengthening }

/-- *plus* — Temporal/quantitative n-word ('no more', 'no longer').
    Same lexeme as positive *plus* 'more'; the negative reading requires
    co-occurrence with *ne* (or *ne*-drop register) and contextual
    triggering. -/
def plus : Item :=
  { form := "plus"
  , licensor := some .weak
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening }

/-! ### Joint -/

/-- The French polarity-item inventory: the Fragment-side joint listing
    every polarity item this fragment defines. -/
def items : List Item :=
  [personne, rien, jamais, plus]

/-! ### Verification -/

/-- Every attested context of every entry is predicted licensed. -/
theorem french_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

end French.PolarityItems
