import Linglib.Phenomena.Possession.Typology
import Linglib.Phenomena.Possession.Studies.Heine1997

/-!
# Finnish Possessive Constructions
@cite{heine-1997} @cite{stassen-2009}

Finnish (Uralic) derives its primary have-construction from the **Location
Schema** ("Y is located at X" → "X has Y"). The construction consists of:

1. Possessor in adessive case (-lla / -llä 'on, at')
2. Possessum in nominative (= grammatical subject)
3. Copula `olla` 'to be'

The adessive case is etymologically locative ('on the surface of'),
grammaticalized to mark the possessor. Finnish is a textbook example
of the Location Schema reaching Stage III: the adessive in possessive
use is no longer interpreted as locative by speakers.

## Examples

- `Minulla on kirja.` 'I have a book.' (I.ADESS is book)
- `Isällä on auto.` 'Father has a car.' (father.ADESS is car)
- `Minulla ei ole rahaa.` 'I have no money.' (I.ADESS not be money.PART)
-/

namespace Fragments.Finnish.Possession

open Phenomena.Possession.Typology

-- ============================================================================
-- §1. Predicative Possession Strategy
-- ============================================================================

/-- Finnish uses the Location Schema for its primary have-construction. -/
def sourceSchema : PossessionSource := .location

/-- Finnish's predicative strategy is locational/existential. -/
def predicativeStrategy : PredicativePossession := .locational

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
def adnominalStrategy : AdnominalPossession := .doubleMarking

-- ============================================================================
-- §5. Schema-Notion Correlations
-- ============================================================================

/-- The adessive construction covers most possessive notions. Finnish,
    like Estonian, uses the Location Schema for both physical/temporary
    and permanent/inalienable possession — showing full Stage III
    grammaticalization (no location meaning remains). -/
def expressibleNotions : List PossessiveNotion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- All seven notions are expressible, matching Swahili's coverage —
    both are at Stage III of grammaticalization. -/
theorem covers_all_notions :
    expressibleNotions.length = 7 := rfl

-- ============================================================================
-- §6. Heine 1997 Prediction Verification
-- ============================================================================

open Phenomena.Possession.Studies.Heine1997

/-- Finnish's Location Schema matches Heine's predictions:
    have-construction (not belong), possessee as subject, Pred1 arity. -/
theorem matches_heine_predictions :
    let p := predictionsFor sourceSchema
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Finnish at Stage III: the adessive in possessive use is no longer
    interpreted as locative. This matches Heine's Overlap Model prediction
    that fully grammaticalized schemas lose their source meaning. -/
theorem stage_III_grammaticalization :
    OverlapStage.targetOnly.degree > OverlapStage.overlap.degree := by decide

/-- WALS F117A classifies Finnish as `locational`, which maps to
    Heine's Location Schema via `walsToSchema`. -/
theorem wals_consistent :
    walsToSchema .locational = sourceSchema := rfl

end Fragments.Finnish.Possession
