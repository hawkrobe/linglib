import Linglib.Features.Possession

/-!
# Russian Possessive Constructions
[stassen-2009] [nichols-1986] [heine-1997]

Russian derives its primary have-construction from the **Location Schema**
("Y is located at X" → "X has Y"). The construction consists of:

1. Preposition `u` 'at, by' + possessor in genitive case
2. Possessum in nominative (= grammatical subject)
3. Copula `est'` 'is' (often omitted in present tense)

The possessor is an oblique locative adjunct; the possessee is the
grammatical subject. This matches [heine-1997]'s prediction: Location
Schema encodes the possessee as subject.

Russian also has a secondary, less common Action Schema construction
using `imet'` 'to have' (< `*em-` 'take'), where the possessor is subject.

PossessionProfile bundle for Russian (ISO `rus`), per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Features/Possession.lean`. Heine 1997 prediction verification for
Russian lives in `Studies/Heine1997.lean`.

## Examples

- `U menja (est') kniga.` 'I have a book.' (at me is book)
- `U menja net deneg.` 'I have no money.' (at me not-is money.GEN)
- `On imeet pravo.` 'He has a right.' (he has.3SG right; Action Schema)
-/

set_option autoImplicit false

namespace Russian.Possession

open _root_.Possession

-- ============================================================================
-- §1. Predicative Possession Strategy
-- ============================================================================

/-- Russian's primary possessive construction uses the Location Schema. -/
def sourceSchema : Source := .location

/-- Russian's predicative strategy is locational/existential. -/
def predicativeStrategy : PredicativeStrategy := .locational

/-- The strategy matches the schema via `predicativeSource`. -/
theorem strategy_matches_schema :
    predicativeSource predicativeStrategy = sourceSchema := rfl

-- ============================================================================
-- §2. The `u` + GEN Construction
-- ============================================================================

/-- Components of the Russian possessive construction. -/
structure RuPossessive where
  /-- The preposition `u` 'at, by' — etymologically locative. -/
  preposition : String := "u"
  /-- Possessor case: genitive (following `u`). -/
  possessorCase : String := "GEN"
  /-- Possessee case: nominative (grammatical subject). -/
  possesseeCase : String := "NOM"
  /-- Copula `est'` — often dropped in present tense affirmative. -/
  copula : String := "est'"
  /-- Negative existential `net` + genitive (replaces `est'` + NOM). -/
  negForm : String := "net"
  deriving DecidableEq, Repr

def primaryConstruction : RuPossessive := {}

-- ============================================================================
-- §3. Secondary: Action Schema (`imet'`)
-- ============================================================================

/-- Russian has a secondary Action Schema construction using `imet'` 'to have'
    (< Proto-Slavic `*jьmati`, related to `*em-` 'take, seize').
    This is restricted to formal/abstract possession and is much less common
    than the `u` + GEN construction. -/
def secondarySchema : Source := .action

/-- `imet'` is transitive: possessor = subject, possessee = object.
    This matches [heine-1997]'s prediction for the Action Schema. -/
def imetPossessorIsSubject : Bool := true

-- ============================================================================
-- §4. Schema-Notion Correlations
-- ============================================================================

/-- The `u` + GEN construction covers most possessive notions in Russian.
    However, physical/temporary possession is its prototypical use (matching
    Location Schema predictions), and abstract possession often prefers
    `imet'` (Action Schema). -/
def uGenNotions : List Notion :=
  [.physical, .temporary, .permanent, .inalienable]

def imetNotions : List Notion :=
  [.abstract, .permanent]

-- ============================================================================
-- §5. Russian Possession Profile (PossessionProfile bundle)
-- ============================================================================

/-- Russian possession profile. -/
def possession : PossessionProfile :=
  { language := "Russian"
  , family := "Indo-European"
  , iso := "rus"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .none
  , examples := ["u menja est' kniga", "kniga Ivana"]
  , notes := "Locational: u + GEN + est'; adnominal: NP-GEN" }

end Russian.Possession
