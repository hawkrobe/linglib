import Linglib.Fragments.Swahili.Basic
import Linglib.Features.Possession

/-!
# Swahili Possessive Constructions
[stassen-2009] [nichols-1986] [heine-1997]

Swahili (Bantu, Niger-Congo) derives its primary have-construction from the
**Companion Schema** ("X is with Y" → "X has Y"). The possessive marker
`-na` is a fusion of the copula `-wa` 'be' and the comitative preposition
`na` 'with'. In the present tense unmarked form, the copula is deleted,
leaving subject prefix + `na` as an unanalyzable possessive marker.

Swahili also has locative noun classes 16 (`pa-`), 17 (`ku-`), and 18 (`mu-`)
that are relevant to possession via the Location Schema, and an Equation
Schema belong-construction using the associative `-a`.

PossessionProfile bundle for Swahili (ISO `swh`), per the project's
"per-language data flows through Fragments" rule. Substrate types live in
`Linglib/Features/Possession.lean`. Heine 1997 prediction verification for
Swahili lives in `Studies/Heine1997.lean`. The
`PossessionProfile.adnominalStrategy = .headMarking` here flattens the
[nichols-1986] categorisation; Swahili's Bantu noun-class concord is
strictly head-marking only in the agreement sense, with the associative
particle `a` carrying class agreement to the possessum.

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

set_option autoImplicit false

namespace Swahili.Possession

open _root_.Possession

-- ============================================================================
-- §1. Predicative Possession Strategy
-- ============================================================================

/-- Swahili uses the Companion Schema for have-constructions:
    subject prefix + `na` (< `-wa na` 'be with'). -/
def sourceSchema : Source := .companion

/-- Swahili's predicative strategy is comitative. -/
def predicativeStrategy : PredicativeStrategy := .comitative

/-- The strategy matches the schema via `predicativeSource`. -/
theorem strategy_matches_schema :
    predicativeSource predicativeStrategy = sourceSchema := rfl

-- ============================================================================
-- §2. The `-na` Paradigm
-- ============================================================================

open Swahili (NounClass)

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
def belongSchema : Source := .equation

/-- The have- and belong-schemas are distinct in Swahili, as predicted
    by Table 2.4: Companion → have only; Equation → belong only. -/
theorem have_belong_distinct :
    sourceSchema ≠ belongSchema := by decide

-- ============================================================================
-- §5. Possessive Notions Expressible
-- ============================================================================

/-- Swahili `-na` covers all seven possessive notions — it is not restricted
    to a subset. This is characteristic of highly grammaticalized have-markers
    ([heine-1997] §2.3). -/
def expressibleNotions : List Notion :=
  [.physical, .temporary, .permanent, .inalienable, .abstract,
   .inanimateInalienable, .inanimateAlienable]

/-- All seven notions are expressible. -/
theorem covers_all_notions :
    expressibleNotions.length = 7 := rfl

-- ============================================================================
-- §6. Swahili Possession Profile (PossessionProfile bundle)
-- ============================================================================

/-- Swahili possession profile.

    Adnominal strategy is encoded as `.headMarking` to match Bantu
    noun-class concord (the associative particle `a` agrees with the
    possessum in class). The strict [nichols-1986] typology would
    classify it differently in some descriptions; we follow the WALS
    convention here. -/
def possession : PossessionProfile :=
  { language := "Swahili"
  , family := "Niger-Congo"
  , iso := "swh"
  , obligatoryPossession := .noObligatory
  , possessiveClassification := .noClassification
  , predicativeStrategy := .comitative
  , adnominalStrategy := .headMarking
  , affixPosition := some .suffixes
  , examples := ["nina kitabu", "kitabu ch-angu"]
  , notes := "Comitative na- for predicative possession; " ++
             "noun-class agreement on possessive for adnominal" }

end Swahili.Possession
