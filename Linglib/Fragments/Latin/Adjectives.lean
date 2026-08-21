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
- **ABB**: suppletive CMPR+SPRL sharing a root (`parvus – minor – minimus`)
- **ABC**: three distinct roots (`bonus – melior – optimus`)

No Latin adjective shows an *ABA pattern. Suppletion is the categorical
replacement of one root by another, not a point on a cline of irregularity:
*magnus – maior – maximus* keeps one root throughout and is not suppletive,
and *malus – pēj-or – pe-ssimus* shares one suppletive root across the two
graded forms ([bobaljik-2012] Table 4.1), so it is ABB.
-/

namespace Latin.Adjectives

open Morphology.Degree (DegreePattern aaa abb abc)

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

/-- *malus – peior – pessimus* ('bad – worse – worst'): ABB — one suppletive
    root *pēj-*/*pe-* in both graded forms ([bobaljik-2012] Table 4.1). -/
def malus : Adjective :=
  { form := "malus"
  , comparison := { formComp := "peior", formSuper := "pessimus", suppletion := abb
                  , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive } }

/-- *magnus – maior – maximus* ('great – greater – greatest'): irregular but
    not suppletive — *mag-*, *mai-*, *max-* are one root, and the triple is
    absent from [bobaljik-2012]'s Table 4.1. AAA. -/
def magnus : Adjective :=
  { form := "magnus"
  , comparison := { formComp := "maior", formSuper := "maximus", suppletion := aaa } }

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

end Latin.Adjectives
