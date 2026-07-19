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

open Reciprocal

def anSuffix : Marker :=
  { form := "-an-", strategy := .verbalAffix }

/-- Marker inventory. -/
def markers : List Marker := [anSuffix]

end Chichewa.Reciprocals
