import Linglib.Phenomena.Possession.Typology
import Linglib.Phenomena.Possession.Studies.Heine1997

/-!
# Turkish Possessive Constructions
@cite{heine-1997} @cite{stassen-2009}

Turkish (Altaic) derives its primary have-construction from the **Genitive
Schema** ("X's Y exists" → "X has Y"). The construction consists of:

1. Possessor in genitive case (`-(n)In`)
2. Possessum with possessive agreement suffix (`-(s)I`)
3. Existential predicate `var` 'existent' (or `yok` 'non-existent')

Turkish also has a Goal Schema variant using dative (`-A`) with
existential `var`, and the Equation Schema for belong-constructions.

## Examples

- `Hasan-ın inek-i var.` 'Hasan has a cow.' (Hasan-GEN cow-POSS existent)
- `Bende kitap var.` 'I have a book.' (at-me book existent; Location variant)
- `Kitab-ım var.` 'I have a book.' (book-POSS.1SG existent; Genitive)
-/

namespace Fragments.Turkish.Possession

open Phenomena.Possession.Typology

-- ============================================================================
-- §1. Predicative Possession Strategy
-- ============================================================================

/-- Turkish uses the Genitive Schema for its primary have-construction:
    GEN-possessor + POSS-possessum + `var`/`yok`. -/
def sourceSchema : PossessionSource := .genitive

/-- Turkish's predicative strategy is genitive/dative (the possessor is
    marked with genitive case, the predicate is a non-verbal existential). -/
def predicativeStrategy : PredicativePossession := .genitiveDative

-- ============================================================================
-- §2. Possessive Agreement Suffixes
-- ============================================================================

/-- Turkish possessive suffix paradigm. These suffixes appear on the
    possessum and agree with the possessor in person and number. -/
inductive PossPerson where
  | first | second | third
  deriving DecidableEq, Repr

inductive PossNumber where
  | sg | pl
  deriving DecidableEq, Repr

/-- Possessive suffix forms (after consonant-final stems). -/
def possSuffix : PossPerson → PossNumber → String
  | .first,  .sg => "-(I)m"
  | .second, .sg => "-(I)n"
  | .third,  .sg => "-(s)I"
  | .first,  .pl => "-(I)mIz"
  | .second, .pl => "-(I)nIz"
  | .third,  .pl => "-lArI"

-- ============================================================================
-- §3. The `var`/`yok` Existential Predicate
-- ============================================================================

/-- The existential predicate in Turkish possessive constructions. -/
inductive ExistPred where
  /-- `var` 'existent, there is' — affirmative possession -/
  | var
  /-- `yok` 'non-existent, there is not' — negative possession -/
  | yok
  deriving DecidableEq, Repr

/-- `var`/`yok` is not a verb — it is a non-verbal predicate that takes
    no tense/aspect morphology in the base form. This is characteristic
    of non-lexical predicate nuclei in Heine's Genitive Schema. -/
def existPredIsNonVerbal : Bool := true

-- ============================================================================
-- §4. Multiple Schemas in Turkish
-- ============================================================================

/-- Turkish also has a Location Schema variant where the possessor
    takes locative case (`-DA`) instead of genitive. This variant
    tends toward physical/temporary possession readings. -/
def locationVariant : PossessionSource := .location

/-- Turkish uses the Equation Schema for belong-constructions with
    genitive predicates: `Kitap Hasan-ın.` 'The book is Hasan's.' -/
def belongSchema : PossessionSource := .equation

/-- Turkish exhibits three schemas, as Heine predicts is common for
    languages that draw on Existence sub-schemas. -/
def attestedSchemas : List PossessionSource :=
  [sourceSchema, locationVariant, belongSchema]

theorem three_schemas :
    attestedSchemas.length = 3 := rfl

-- ============================================================================
-- §5. Schema-Notion Correlations in Turkish
-- ============================================================================

/-- The Genitive Schema in Turkish is used for permanent, inalienable,
    and abstract possession. Physical/temporary possession is expressed
    by the Location Schema variant with locative case. This matches
    Heine's generalizations: Existence schemas correlate with
    permanent/inalienable notions; Location with physical/temporary. -/
def genitiveNotions : List PossessiveNotion :=
  [.permanent, .inalienable, .abstract]

def locationNotions : List PossessiveNotion :=
  [.physical, .temporary]

/-- Genitive Schema does not express physical possession in Turkish. -/
theorem genitive_not_physical :
    ¬genitiveNotions.contains .physical := by native_decide

/-- Location Schema does not express inalienable possession in Turkish. -/
theorem location_not_inalienable :
    ¬locationNotions.contains .inalienable := by native_decide

-- ============================================================================
-- §6. Heine 1997 Prediction Verification
-- ============================================================================

open Phenomena.Possession.Studies.Heine1997

/-- Turkish's primary Genitive Schema matches Heine's predictions:
    have-construction (not belong), possessee as subject. -/
theorem genitive_matches_heine :
    let p := predictionsFor sourceSchema
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Heine predicts Genitive Schema correlates with permanent/inalienable
    notions. Turkish's genitive notions match this. -/
theorem genitive_notions_match_prediction :
    (schemaTypicalNotions sourceSchema).contains .permanent = true ∧
    (schemaTypicalNotions sourceSchema).contains .inalienable = true := by
  native_decide

/-- Heine predicts Location Schema correlates with physical/temporary
    notions. Turkish's location variant notions match this. -/
theorem location_notions_match_prediction :
    (schemaTypicalNotions locationVariant).contains .physical = true ∧
    (schemaTypicalNotions locationVariant).contains .temporary = true := by
  native_decide

/-- WALS F117A classifies Turkish as `genitive`, matching our
    primary Genitive Schema. -/
theorem wals_consistent :
    walsToSchema .genitive = sourceSchema := rfl

end Fragments.Turkish.Possession
