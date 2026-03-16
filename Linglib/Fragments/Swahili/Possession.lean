import Linglib.Phenomena.Possession.Typology

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

/-- Swahili noun classes relevant to subject agreement in possessive
    constructions. Classes 1/2 are human singular/plural. -/
inductive NounClass where
  | cl1   -- m- (human sg): a-na
  | cl2   -- wa- (human pl): wa-na
  | cl3   -- m- (tree sg): u-na
  | cl4   -- mi- (tree pl): i-na
  | cl5   -- ji-/∅ (augmentative sg): li-na
  | cl6   -- ma- (augmentative pl): ya-na
  | cl7   -- ki- (diminutive sg): ki-na
  | cl8   -- vi- (diminutive pl): vi-na
  | cl9   -- n- (animal sg): i-na
  | cl10  -- n- (animal pl): zi-na
  | cl15  -- ku- (infinitive): ku-na
  | cl16  -- pa- (definite location): pa-na
  | cl17  -- ku- (indefinite location): ku-na
  | cl18  -- mu-/m- (inside location): mu-na
  deriving DecidableEq, BEq, Repr

/-- Subject prefix for each class in the `-na` construction. -/
def subjPrefix : NounClass → String
  | .cl1  => "a"
  | .cl2  => "wa"
  | .cl3  => "u"
  | .cl4  => "i"
  | .cl5  => "li"
  | .cl6  => "ya"
  | .cl7  => "ki"
  | .cl8  => "vi"
  | .cl9  => "i"
  | .cl10 => "zi"
  | .cl15 => "ku"
  | .cl16 => "pa"
  | .cl17 => "ku"
  | .cl18 => "mu"

/-- The possessive form: subject prefix + "na". -/
def possessiveForm (c : NounClass) : String :=
  subjPrefix c ++ "na"

/-- First-person singular and plural forms use special prefixes. -/
def possForm1sg : String := "nina"
def possForm1pl : String := "tuna"
def possForm2sg : String := "una"
def possForm2pl : String := "mna"

-- ============================================================================
-- §3. Locative Classes and Possession
-- ============================================================================

/-- Whether a noun class is a locative class (16, 17, 18).
    These classes provide the locative predicate in the Location Schema
    and also serve as impersonal subjects in existential constructions. -/
def NounClass.isLocative : NounClass → Bool
  | .cl16 | .cl17 | .cl18 => true
  | _ => false

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

end Fragments.Swahili.Possession
