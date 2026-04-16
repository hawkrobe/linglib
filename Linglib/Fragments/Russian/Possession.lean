import Linglib.Phenomena.Possession.Typology
import Linglib.Phenomena.Possession.Studies.Heine1997

/-!
# Russian Possessive Constructions
@cite{heine-1997} @cite{stassen-2009}

Russian derives its primary have-construction from the **Location Schema**
("Y is located at X" → "X has Y"). The construction consists of:

1. Preposition `u` 'at, by' + possessor in genitive case
2. Possessum in nominative (= grammatical subject)
3. Copula `est'` 'is' (often omitted in present tense)

The possessor is an oblique locative adjunct; the possessee is the
grammatical subject. This matches Heine's prediction: Location Schema
encodes the possessee as subject.

Russian also has a secondary, less common Action Schema construction
using `imet'` 'to have' (< `*em-` 'take'), where the possessor is subject.

## Examples

- `U menja (est') kniga.` 'I have a book.' (at me is book)
- `U menja net deneg.` 'I have no money.' (at me not-is money.GEN)
- `On imeet pravo.` 'He has a right.' (he has.3SG right; Action Schema)
-/

namespace Fragments.Russian.Possession

open Phenomena.Possession.Typology

-- ============================================================================
-- §1. Primary: Location Schema
-- ============================================================================

/-- Russian's primary possessive construction uses the Location Schema. -/
def sourceSchema : PossessionSource := .location

/-- Russian's predicative strategy is locational/existential. -/
def predicativeStrategy : PredicativePossession := .locational

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
def secondarySchema : PossessionSource := .action

/-- `imet'` is transitive: possessor = subject, possessee = object.
    This matches Heine's prediction for the Action Schema. -/
def imetPossessorIsSubject : Bool := true

-- ============================================================================
-- §4. The Overlap Model in Russian
-- ============================================================================

/-- Russian illustrates Heine's Overlap Model clearly. The `u` construction
    shows all three stages depending on context:

    - Stage I (source only): `Lampa stoit u okna.` 'The lamp stands by the
      window.' — pure location, no possessive meaning.
    - Stage II (overlap): `Sejcas u Markovyx gripp.` 'There is flu at the
      Markovs / The Markovs have the flu.' — ambiguous.
    - Stage III (target only): `U Peti est' masina.` 'Peter has a car.' —
      possessive meaning only, no locative reading. -/
inductive RuOverlapExample where
  | stageI   -- `Lampa stoit u okna.` (pure location)
  | stageII  -- `Sejcas u Markovyx gripp.` (ambiguous)
  | stageIII -- `U Peti est' masina.` (possession only)
  deriving DecidableEq, Repr

-- ============================================================================
-- §5. Schema-Notion Correlations
-- ============================================================================

/-- The `u` + GEN construction covers most possessive notions in Russian.
    However, physical/temporary possession is its prototypical use (matching
    Location Schema predictions), and abstract possession often prefers
    `imet'` (Action Schema). -/
def uGenNotions : List PossessiveNotion :=
  [.physical, .temporary, .permanent, .inalienable]

def imetNotions : List PossessiveNotion :=
  [.abstract, .permanent]

-- ============================================================================
-- §6. Heine 1997 Prediction Verification
-- ============================================================================

open Heine1997

/-- Russian's primary Location Schema matches Heine's predictions:
    have-construction (not belong), possessee as subject. -/
theorem primary_matches_heine :
    let p := predictionsFor sourceSchema
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Russian's secondary Action Schema can yield both have and belong,
    matching Heine's Table 2.4. -/
theorem secondary_is_dual :
    schemaYieldsHave secondarySchema = true ∧
    schemaYieldsBelong secondarySchema = true := by
  exact ⟨rfl, rfl⟩

/-- The `u` construction coexists across all three Overlap stages in
    Russian, matching the paper's example (73a-d). Stage I and III
    are strictly ordered. -/
theorem overlap_stages_ordered :
    OverlapStage.sourceOnly.degree < OverlapStage.overlap.degree ∧
    OverlapStage.overlap.degree < OverlapStage.targetOnly.degree := by
  exact ⟨by decide, by decide⟩

/-- WALS F117A classifies Russian as `locational`, matching our
    primary Location Schema. -/
theorem wals_consistent :
    walsToSchema .locational = sourceSchema := rfl

end Fragments.Russian.Possession
