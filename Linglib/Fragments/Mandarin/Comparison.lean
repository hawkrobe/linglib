import Linglib.Syntax.Comparative

/-!
# Mandarin comparative data

Mandarin compares with *X bǐ Y Adj* (WALS Ch 121A: exceed, [stassen-2013]):
the standard is the object of *bǐ*, and the free degree word *gèng* 'even
more' is available. No superlative strategy is recorded: the free superlative
word *zuì* fits none of `SuperlativeStrategy`'s cases.
-/

set_option autoImplicit false

namespace Mandarin.Comparison

open Comparative

/-- The *bǐ*-comparative: the standard is *bǐ*'s object. -/
def bi : Comparative :=
  { standardMarker := some "bi"
  , caseAssignment := .fixed
  , fixedEncoding := some .directObject
  , degreeMarker := some "geng" }

/-- Free degree word *gèng*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

end Mandarin.Comparison
