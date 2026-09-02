import Linglib.Fragments.Swahili.Basic

/-!
# Swahili Possessive Constructions
[stassen-2009] [nichols-1986] [heine-1997]

Swahili (Bantu, Niger-Congo) derives its primary have-construction from the
**Companion Schema** ("X is with Y" → "X has Y"). The possessive marker
`-na` is a fusion of the copula `-wa` 'be' and the comitative preposition
`na` 'with'. In the present tense unmarked form, the copula is deleted,
leaving subject prefix + `na` as an unanalyzable possessive marker.
Swahili also has locative noun classes 16 (`pa-`), 17 (`ku-`), and 18 (`mu-`)
that take the same `-na` marker, and an Equation Schema belong-construction
using the associative `-a` (`Saa ni y-angu.` 'The watch is mine.'). The
typological codings (WALS 24A, 58A, 59A, 117A) are read from
`Data/WALS/Features/`; this file holds the `-na` paradigm.

## Possessive paradigm

| Person | Singular | Plural |
|--------|----------|--------|
| 1st    | ni-na    | tu-na  |
| 2nd    | u-na     | m-na   |
| 3rd    | a-na     | wa-na  |

## Examples

- `Nina kitabu.` 'I have a book.' (Companion: I-with book)
- `Ana na watoto wawili.` 'He/she has two children.' (lit. 'is with children two')
-/

namespace Swahili.Possession

open Swahili (NounClass)

/-- The possessive form: subject prefix + "na". -/
def possessiveForm (c : NounClass) : String :=
  c.subjPrefix ++ "na"

/-- First-person singular and plural forms use special prefixes. -/
def possForm1sg : String := "nina"
def possForm1pl : String := "tuna"
def possForm2sg : String := "una"
def possForm2pl : String := "mna"

/-- Locative classes use the same `-na` marker for "there is ... with",
    illustrating how Companion and Location schemas overlap in Swahili. -/
theorem locative_uses_na :
    possessiveForm .cl16 = "pana" ∧
    possessiveForm .cl17 = "kuna" ∧
    possessiveForm .cl18 = "muna" := ⟨rfl, rfl, rfl⟩

end Swahili.Possession
