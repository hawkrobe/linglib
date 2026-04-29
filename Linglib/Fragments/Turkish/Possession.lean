import Linglib.Typology.Possession

/-!
# Turkish Possessive Constructions
@cite{stassen-2009} @cite{nichols-1986} @cite{heine-1997}

Turkish (Altaic) derives its primary have-construction from the **Genitive
Schema** ("X's Y exists" → "X has Y"). The construction consists of:

1. Possessor in genitive case (`-(n)In`)
2. Possessum with possessive agreement suffix (`-(s)I`)
3. Existential predicate `var` 'existent' (or `yok` 'non-existent')

Turkish also has a Goal Schema variant using dative (`-A`) with
existential `var`, and the Equation Schema for belong-constructions.

PossessionProfile bundle for Turkish (ISO `tur`), per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Typology/Possession.lean`. Heine 1997 prediction verification for
Turkish lives in `Phenomena/Possession/Studies/Heine1997.lean`.

## Examples

- `Hasan-ın inek-i var.` 'Hasan has a cow.' (Hasan-GEN cow-POSS existent)
- `Bende kitap var.` 'I have a book.' (at-me book existent; Location variant)
- `Kitab-ım var.` 'I have a book.' (book-POSS.1SG existent; Genitive)
-/

set_option autoImplicit false

namespace Fragments.Turkish.Possession

open _root_.Typology.Possession

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
    of non-lexical predicate nuclei in @cite{heine-1997}'s Genitive Schema. -/
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

/-- Turkish exhibits three schemas, as @cite{heine-1997} predicts is common
    for languages that draw on Existence sub-schemas. -/
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
    @cite{heine-1997}'s generalizations: Existence schemas correlate with
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
-- §6. Turkish Possession Profile (PossessionProfile bundle)
-- ============================================================================

/-- Turkish possession profile.

    Note: Turkish's primary construction (`Hasan-ın inek-i var`) is
    @cite{heine-1997}'s Genitive Schema, encoded as `.genitiveDative`
    in @cite{stassen-2009}'s WALS Ch 117 typology. -/
def possession : PossessionProfile :=
  { language := "Turkish"
  , family := "Turkic"
  , iso := "tur"
  , obligatoryPossession := .exists_
  , possessiveClassification := .noClassification
  , predicativeStrategy := .genitiveDative
  , adnominalStrategy := .doubleMarking
  , affixPosition := some .suffixes
  , examples := ["(benim) kitab-im var", "Ali-nin kitab-i"]
  , notes := "var/yok existential predicate; GEN on possessor + " ++
             "possessive suffix on head (double-marking)" }

end Fragments.Turkish.Possession
