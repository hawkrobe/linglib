import Linglib.Morphology.MorphRule
import Linglib.Syntax.Reciprocal

/-!
# Chicheŵa Reciprocal Fragment
[nordlinger-2023]

Chicheŵa (Bantu) marks reciprocity with the verbal affix "-an-" (same
cognate as Swahili "-an-", reflecting shared Bantu morphology). This is
a verbal affix strategy (monovalent): it reduces valency by removing the
object argument.

Example: [nordlinger-2023] ex. 20 (citing Dalrymple et al. 1994).

The reciprocal affix is distinct from the reflexive prefix "dzi-".
-/

namespace Chichewa.Reciprocals

open Morphology

/-- Chicheŵa reciprocal suffix "-an-" as a morphological rule. -/
def reciprocalAffix : MorphRule Bool :=
  { category := .valence
  , value := "reciprocal"
  , formRule := fun stem => stem ++ "an"
  , featureRule := id
  , valenceRule := fun _ => some ComplementType.none
  , semEffect := id
  }

/-- Chicheŵa reflexive prefix "dzi-" (for contrast). -/
def reflexivePrefix : MorphRule Bool :=
  { category := .valence
  , value := "reflexive"
  , formRule := fun stem => "dzi" ++ stem
  , featureRule := id
  , valenceRule := fun _ => some ComplementType.none
  , semEffect := id
  }

/-- Reciprocal and reflexive are formally distinct in Chicheŵa. -/
theorem recip_distinct_from_reflexive :
    reciprocalAffix.value ≠ reflexivePrefix.value := by decide

open Reciprocal

/-- The reciprocal suffix as a typological marker (distinct from the
    reflexive *dzi-*). -/
def anSuffix : ReciprocalMarker :=
  { form := "-an-", strategy := .verbalAffix }

/-- Marker inventory. -/
def markers : List ReciprocalMarker := [anSuffix]

end Chichewa.Reciprocals
