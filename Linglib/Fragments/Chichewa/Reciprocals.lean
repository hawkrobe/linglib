import Linglib.Core.Morphology.MorphRule

/-!
# Chicheŵa Reciprocal Fragment
@cite{nordlinger-2023}

Chicheŵa (Bantu) marks reciprocity with the verbal affix "-an-" (same
cognate as Swahili "-an-", reflecting shared Bantu morphology). This is
a verbal affix strategy (monovalent): it reduces valency by removing the
object argument.

Example: @cite{nordlinger-2023} ex. 20 (citing Dalrymple et al. 1994).

The reciprocal affix is distinct from the reflexive prefix "dzi-".
-/

namespace Fragments.Chichewa.Reciprocals

open Core.Morphology

/-- Chicheŵa reciprocal suffix "-an-" as a morphological rule. -/
def reciprocalAffix : MorphRule Bool :=
  { category := .valence
  , value := "reciprocal"
  , formRule := fun stem => stem ++ "an"
  , featureRule := fun f => { f with valence := some .intransitive }
  , semEffect := id
  }

/-- Chicheŵa reflexive prefix "dzi-" (for contrast). -/
def reflexivePrefix : MorphRule Bool :=
  { category := .valence
  , value := "reflexive"
  , formRule := fun stem => "dzi" ++ stem
  , featureRule := fun f => { f with valence := some .intransitive }
  , semEffect := id
  }

/-- Reciprocal and reflexive are formally distinct in Chicheŵa. -/
theorem recip_distinct_from_reflexive :
    reciprocalAffix.value ≠ reflexivePrefix.value := by decide

end Fragments.Chichewa.Reciprocals
