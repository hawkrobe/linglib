import Linglib.Syntax.Category.Adjective.Basic

/-!
# Latin Adjective Degree Forms
[bobaljik-2012]

Latin comparative and superlative morphology, used for cross-linguistic
verification of [bobaljik-2012]'s *ABA constraint and pattern inventory. Latin
adjectives instantiate the general `Adjective` object (`Syntax/Category/Adjective/Basic.lean`),
carrying their morphology in the `comparison` facet; the data here is purely
morphological (no scale `dimension`).

Latin exhibits all three attested degree suppletion patterns:

- **AAA**: regular (`longus – longior – longissimus`)
- **ABB**: suppletive CMPR+SPRL sharing a root (`magnus – maior – maximus`)
- **ABC**: three distinct roots (`bonus – melior – optimus`)

No Latin adjective shows an *ABA pattern.
-/

namespace Latin.Adjectives

open Morphology.DegreeContainment (DegreePattern aaa abb abc)

-- ============================================================================
-- § 1: Regular Adjectives (AAA)
-- ============================================================================

/-- *longus – longior – longissimus* ('long'): regular synthetic
    comparative and superlative with productive suffixes *-ior*/*-issimus*. -/
def longus : Adjective :=
  { form := "longus"
  , comparison := { formComp := "longior", formSuper := "longissimus", suppletion := aaa } }

/-- *altus – altior – altissimus* ('tall/high/deep'): regular. -/
def altus : Adjective :=
  { form := "altus"
  , comparison := { formComp := "altior", formSuper := "altissimus", suppletion := aaa } }

/-- *fortis – fortior – fortissimus* ('brave/strong'): regular. -/
def fortis : Adjective :=
  { form := "fortis"
  , comparison := { formComp := "fortior", formSuper := "fortissimus", suppletion := aaa } }

-- ============================================================================
-- § 2: Suppletive Adjectives
-- ============================================================================

/-- *bonus – melior – optimus* ('good – better – best'): three distinct
    roots (ABC), the paradigmatic ABC example ([bobaljik-2012]). Both grades
    suppletive. -/
def bonus : Adjective :=
  { form := "bonus"
  , comparison := { formComp := "melior", formSuper := "optimus", suppletion := abc
                  , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive } }

/-- *malus – peior – pessimus* ('bad – worse – worst'): three distinct roots (ABC). -/
def malus : Adjective :=
  { form := "malus"
  , comparison := { formComp := "peior", formSuper := "pessimus", suppletion := abc
                  , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive } }

/-- *magnus – maior – maximus* ('great – greater – greatest'): ABB — the
    comparative and superlative share the suppletive root *mai-*/*max-*. -/
def magnus : Adjective :=
  { form := "magnus"
  , comparison := { formComp := "maior", formSuper := "maximus", suppletion := abb
                  , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive } }

/-- *parvus – minor – minimus* ('small – smaller – smallest'): ABB, suppletive
    root *min-* shared across comparative and superlative. -/
def parvus : Adjective :=
  { form := "parvus"
  , comparison := { formComp := "minor", formSuper := "minimus", suppletion := abb
                  , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive } }

-- ============================================================================
-- § 3: Fragment Inventory
-- ============================================================================

def allEntries : List Adjective :=
  [longus, altus, fortis, bonus, malus, magnus, parvus]

-- ============================================================================
-- § 4: Contiguity Verification
-- ============================================================================

/-- All Latin entries satisfy contiguity (no *ABA). -/
theorem latin_no_aba :
    ∀ e ∈ allEntries, e.suppletion.IsContiguous := by decide

/-- Regular entries derive AAA patterns. -/
theorem longus_aaa : longus.suppletion = aaa := rfl
theorem altus_aaa : altus.suppletion = aaa := rfl
theorem fortis_aaa : fortis.suppletion = aaa := rfl

/-- bonus/melior/optimus is ABC. -/
theorem bonus_abc : bonus.suppletion = abc := rfl

/-- malus/peior/pessimus is ABC. -/
theorem malus_abc : malus.suppletion = abc := rfl

/-- magnus/maior/maximus is ABB. -/
theorem magnus_abb : magnus.suppletion = abb := rfl

/-- parvus/minor/minimus is ABB. -/
theorem parvus_abb : parvus.suppletion = abb := rfl

/-- Latin has all three attested patterns: AAA, ABB, ABC. -/
theorem latin_has_aaa : allEntries.any (λ e => e.suppletion == aaa) = true := by decide
theorem latin_has_abb : allEntries.any (λ e => e.suppletion == abb) = true := by decide
theorem latin_has_abc : allEntries.any (λ e => e.suppletion == abc) = true := by decide

end Latin.Adjectives
