import Linglib.Theories.Morphology.DegreeContainment

/-!
# Latin Adjective Degree Forms
@cite{bobaljik-2012}

Latin comparative and superlative morphology, used for cross-linguistic
verification of @cite{bobaljik-2012}'s *ABA constraint and pattern
inventory.

Latin exhibits all three attested degree suppletion patterns:

- **AAA**: regular (`longus – longior – longissimus`)
- **ABB**: suppletive CMPR+SPRL sharing a root (`magnus – maior – maximus`)
- **ABC**: three distinct roots (`bonus – melior – optimus`)

No Latin adjective shows an *ABA pattern.
-/

namespace Fragments.Latin.Adjectives

open Morphology.DegreeContainment

-- ============================================================================
-- § 1: Latin Adjective Entry
-- ============================================================================

/-- A Latin adjective entry with positive, comparative, and superlative
    forms plus the suppletive pattern. Minimal structure — Latin data
    here is purely morphological (no scale type, dimension, etc.). -/
structure LatinAdjEntry where
  pos  : String
  cmpr : String
  sprl : String
  suppletion : DegreePattern
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: Regular Adjectives (AAA)
-- ============================================================================

/-- *longus – longior – longissimus* ('long'): regular synthetic
    comparative and superlative with productive suffixes *-ior*/*-issimus*. -/
def longus : LatinAdjEntry :=
  { pos := "longus", cmpr := "longior", sprl := "longissimus"
  , suppletion := aaa }

/-- *altus – altior – altissimus* ('tall/high/deep'): regular. -/
def altus : LatinAdjEntry :=
  { pos := "altus", cmpr := "altior", sprl := "altissimus"
  , suppletion := aaa }

/-- *fortis – fortior – fortissimus* ('brave/strong'): regular. -/
def fortis : LatinAdjEntry :=
  { pos := "fortis", cmpr := "fortior", sprl := "fortissimus"
  , suppletion := aaa }

-- ============================================================================
-- § 3: Suppletive Adjectives
-- ============================================================================

/-- *bonus – melior – optimus* ('good – better – best'): three distinct
    roots (ABC). The paradigmatic example of ABC suppletion
    (@cite{bobaljik-2012}). -/
def bonus : LatinAdjEntry :=
  { pos := "bonus", cmpr := "melior", sprl := "optimus"
  , suppletion := abc }

/-- *malus – peior – pessimus* ('bad – worse – worst'): three distinct
    roots (ABC). -/
def malus : LatinAdjEntry :=
  { pos := "malus", cmpr := "peior", sprl := "pessimus"
  , suppletion := abc }

/-- *magnus – maior – maximus* ('great – greater – greatest'): ABB.
    The comparative and superlative share the suppletive root *mai-*/*max-*. -/
def magnus : LatinAdjEntry :=
  { pos := "magnus", cmpr := "maior", sprl := "maximus"
  , suppletion := abb }

/-- *parvus – minor – minimus* ('small – smaller – smallest'): ABB.
    Suppletive root *min-* shared across comparative and superlative. -/
def parvus : LatinAdjEntry :=
  { pos := "parvus", cmpr := "minor", sprl := "minimus"
  , suppletion := abb }

-- ============================================================================
-- § 4: Fragment Inventory
-- ============================================================================

def allEntries : List LatinAdjEntry :=
  [longus, altus, fortis, bonus, malus, magnus, parvus]

-- ============================================================================
-- § 5: Contiguity Verification
-- ============================================================================

/-- All Latin entries satisfy contiguity (no *ABA). -/
theorem latin_no_aba :
    allEntries.all (λ e => e.suppletion.isContiguous) = true := by native_decide

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
theorem latin_has_aaa : allEntries.any (λ e => e.suppletion == aaa) = true := by native_decide
theorem latin_has_abb : allEntries.any (λ e => e.suppletion == abb) = true := by native_decide
theorem latin_has_abc : allEntries.any (λ e => e.suppletion == abc) = true := by native_decide

end Fragments.Latin.Adjectives
