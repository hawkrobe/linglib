import Linglib.Syntax.Comparative

/-!
# Korean comparison

Korean compares with the standard marked by the particle *-boda* 'from, than', of separative
origin, and the adjective in its bare form, with the adverb *deo* 'more' as an optional
intensifier: *Yenghi-ga Chelswu-boda (deo) khu-ta* 'Yenghi is taller than Chelswu'. It is a
separative comparative in Stassen's typology, and the superlative is the comparative with a
universal standard.

## References

* [stassen-1985]
-/

namespace Korean.Comparison

open Comparative

/-- The *-boda* comparative: separative postposition-marked standard, no
    degree morphology. -/
def boda : Comparative :=
  { standardMarker := some "-boda"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

/-- No overt degree marking; the adverb *deo* is an optional intensifier. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative as comparative with universal standard. -/
def superlative : SuperlativeStrategy := .comparativeUniversal

end Korean.Comparison
