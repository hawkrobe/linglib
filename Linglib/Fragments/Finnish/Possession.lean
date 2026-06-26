import Linglib.Features.Number.Basic
import Linglib.Features.Possession

/-!
# Finnish Possessive Constructions
[stassen-2009] [nichols-1986] [heine-1997]

Finnish (Uralic) derives its primary have-construction from the **Location
Schema** ("Y is located at X" → "X has Y"). The construction consists of:

1. Possessor in adessive case (-lla / -llä 'on, at')
2. Possessum in nominative (= grammatical subject)
3. Copula `olla` 'to be'

The adessive case is etymologically locative ('on the surface of'),
grammaticalized to mark the possessor. Finnish is a textbook example
of the Location Schema reaching Stage III: the adessive in possessive
use is no longer interpreted as locative by speakers
([heine-1997] Overlap Model).

PossessionProfile bundle for Finnish (ISO `fin`), per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Features/Possession.lean`. Heine 1997 prediction verification for
Finnish lives in `Studies/Heine1997.lean`.

## Examples

- `Minulla on kirja.` 'I have a book.' (I.ADESS is book)
- `Isällä on auto.` 'Father has a car.' (father.ADESS is car)
- `Minulla ei ole rahaa.` 'I have no money.' (I.ADESS not be money.PART)
-/

set_option autoImplicit false

namespace Finnish.Possession

open _root_.Possession

-- ============================================================================
-- §1. Predicative Possession Strategy
-- ============================================================================

/-- Finnish uses the Location Schema for its primary have-construction. -/
def sourceSchema : Source := .location

/-- Finnish's predicative strategy is locational/existential. -/
def predicativeStrategy : PredicativeStrategy := .locational

/-- The strategy matches the schema via `predicativeSource`. -/
theorem strategy_matches_schema :
    predicativeSource predicativeStrategy = sourceSchema := rfl

-- ============================================================================
-- §2. The Adessive Construction
-- ============================================================================

/-- Components of the Finnish possessive construction. -/
structure FiPossessive where
  /-- Possessor case: adessive (`-lla`, `-llä`; vowel harmony). -/
  possessorCase : String := "ADESS"
  /-- Possessee case: nominative (subject of existential). -/
  possesseeCase : String := "NOM"
  /-- Copula: `olla` 'to be'. -/
  copula : String := "olla"
  /-- Negative auxiliary: `ei` (person-inflected) + `ole` (connegative). -/
  negAux : String := "ei"
  /-- In negative, possessee takes partitive case instead of nominative. -/
  negPossesseeCase : String := "PART"
  deriving DecidableEq, Repr

def primaryConstruction : FiPossessive := {}

-- ============================================================================
-- §3. Possessive Suffixes (Attributive)
-- ============================================================================

/-- Finnish possessive suffixes on the possessum (attributive possession).
    These are declining in spoken Finnish but required in formal/written
    registers. -/
inductive FiPossPerson where | first | second | third
  deriving DecidableEq, Repr

inductive FiPossNumber where | sg | pl
  deriving DecidableEq, Repr

/-- The possessive paradigm's number dimension, canonically. -/
def FiPossNumber.toNumber : FiPossNumber → Number
  | .sg => .singular
  | .pl => .plural

def possSuffix : FiPossPerson → FiPossNumber → String
  | .first,  .sg => "-ni"
  | .second, .sg => "-si"
  | .third,  _   => "-nsa/-nsä"
  | .first,  .pl => "-mme"
  | .second, .pl => "-nne"

-- ============================================================================
-- §4. Adnominal Possession Marking
-- ============================================================================

/-- Finnish marks possession on the possessum (head-marking) via the
    possessive suffixes above. It also uses the genitive case on the
    possessor NP (dependent-marking), giving a double-marking pattern
    in formal registers: `Matti-n kirja-nsa` 'Matti-GEN book-POSS.3'. -/
def adnominalStrategy : AdnominalMarking := .doubleMarking

-- ============================================================================
-- §5. Schema-Notion Correlations
-- ============================================================================

/-- The adessive construction covers most possessive notions. Finnish,
    like Estonian, uses the Location Schema for both physical/temporary
    and permanent/inalienable possession — showing full Stage III
    grammaticalization (no location meaning remains). -/
def expressibleNotions : List Notion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- All seven notions are expressible, matching Swahili's coverage —
    both are at Stage III of grammaticalization. -/
theorem covers_all_notions :
    expressibleNotions.length = 7 := rfl

-- ============================================================================
-- §6. Finnish Possession Profile (PossessionProfile bundle)
-- ============================================================================

/-- Finnish possession profile. -/
def possession : PossessionProfile :=
  { language := "Finnish"
  , family := "Uralic"
  , iso := "fin"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .locational
  , adnominalStrategy := .dependentMarking
  , affixPosition := some .suffixes
  , examples := ["minu-lla on kirja", "Matin kirja"]
  , notes := "Adessive -lla for locational predicative possession; " ++
             "genitive + optional possessive suffix on head" }

end Finnish.Possession
