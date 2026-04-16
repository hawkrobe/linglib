import Linglib.Fragments.Swahili.Basic
import Linglib.Phenomena.Possession.Typology
import Linglib.Phenomena.Possession.Studies.Heine1997

/-!
# Swahili Possessive Constructions
@cite{heine-1997} @cite{stassen-2009}

Swahili (Bantu, Niger-Congo) derives its primary have-construction from the
**Companion Schema** ("X is with Y" → "X has Y"). The possessive marker
`-na` is a fusion of the copula `-wa` 'be' and the comitative preposition
`na` 'with'. In the present tense unmarked form, the copula is deleted,
leaving subject prefix + `na` as an unanalyzable possessive marker.

Swahili also has locative noun classes 16 (`pa-`), 17 (`ku-`), and 18 (`mu-`)
that are relevant to possession via the Location Schema, and an Equation
Schema belong-construction using the associative `-a`.

## Possessive paradigm

| Person | Singular | Plural |
|--------|----------|--------|
| 1st    | ni-na    | tu-na  |
| 2nd    | u-na     | m-na   |
| 3rd    | a-na     | wa-na  |

## Examples

- `Nina kitabu.` 'I have a book.' (Companion: I-with book)
- `Ana na watoto wawili.` 'He/she has two children.' (lit. 'is with children two')
- `Saa ni y-angu.` 'The watch is mine.' (Equation: watch is of-me)
-/

namespace Fragments.Swahili.Possession

open Phenomena.Possession.Typology

-- ============================================================================
-- §1. Predicative Possession Strategy
-- ============================================================================

/-- Swahili uses the Companion Schema for have-constructions:
    subject prefix + `na` (< `-wa na` 'be with'). -/
def sourceSchema : PossessionSource := .companion

/-- Swahili's predicative strategy is comitative. -/
def predicativeStrategy : PredicativePossession := .comitative

/-- The strategy matches the schema via `predicativeSource`. -/
theorem strategy_matches_schema :
    predicativeSource predicativeStrategy = sourceSchema := rfl

-- ============================================================================
-- §2. The `-na` Paradigm
-- ============================================================================

open Fragments.Swahili (NounClass)

/-- The possessive form: subject prefix + "na". -/
def possessiveForm (c : NounClass) : String :=
  c.subjPrefix ++ "na"

/-- First-person singular and plural forms use special prefixes. -/
def possForm1sg : String := "nina"
def possForm1pl : String := "tuna"
def possForm2sg : String := "una"
def possForm2pl : String := "mna"

-- ============================================================================
-- §3. Locative Classes and Possession
-- ============================================================================

/-- Locative classes use the same `-na` marker for "there is ... with",
    illustrating how Companion and Location schemas overlap in Swahili. -/
theorem locative_uses_na :
    possessiveForm .cl16 = "pana" ∧
    possessiveForm .cl17 = "kuna" ∧
    possessiveForm .cl18 = "muna" := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §4. Equation Schema: the Associative `-a`
-- ============================================================================

/-- Swahili's belong-construction uses the associative marker `-a`,
    with class-conditioned agreement: `ni y-angu` 'is of-me' (cl9).
    This is an instance of the Equation Schema: "Y is X's (property)". -/
def belongSchema : PossessionSource := .equation

/-- The have- and belong-schemas are distinct in Swahili, as predicted
    by Table 2.4: Companion → have only; Equation → belong only. -/
theorem have_belong_distinct :
    sourceSchema ≠ belongSchema := by decide

-- ============================================================================
-- §5. Possessive Notions Expressible
-- ============================================================================

/-- Swahili `-na` covers all seven possessive notions — it is not restricted
    to a subset. This is characteristic of highly grammaticalized have-markers
    (@cite{heine-1997} §2.3). -/
def expressibleNotions : List PossessiveNotion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- All seven notions are expressible. -/
theorem covers_all_notions :
    expressibleNotions.length = 7 := rfl

-- ============================================================================
-- §6. Heine 1997 Prediction Verification
-- ============================================================================

open Heine1997

/-- Swahili's Companion Schema matches Heine's predictions:
    have-construction (not belong), possessor as subject, Pred2. -/
theorem companion_matches_heine :
    let p := predictionsFor sourceSchema
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = true ∧ p.arity = .pred2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Swahili is at Stage III: the `-na` marker is no longer decomposable
    into copula + comitative, so the source meaning (accompaniment) is
    no longer available. All seven notions expressible confirms full
    grammaticalization. -/
theorem full_grammaticalization :
    expressibleNotions.length = 7 ∧
    OverlapStage.targetOnly.degree = 2 := by
  exact ⟨rfl, rfl⟩

/-- WALS F117A classifies Swahili as `conjunctional` (Stassen's term
    for comitative-based possession), which maps to Heine's Companion
    Schema via `walsToSchema`. -/
theorem wals_consistent :
    walsToSchema .conjunctional = sourceSchema := rfl

end Fragments.Swahili.Possession
