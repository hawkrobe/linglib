import Linglib.Syntax.Comparative

/-!
# Korean comparison

Korean has no adjectival affix like English *-er*. Comparison is made with the particle *-boda*
'than' after the noun phrase compared with, of separative origin, and the adjective in its bare
form, *Yongho-ga Minca-boda keu-da* 'Yongho is taller than Minca', with the adverb *deo* 'more'
as an optional intensifier and the standard and the compared phrase free to scramble, as Sohn
describes it. It is a separative comparative in Stassen's typology, and the superlative is the
comparative with a universal standard. Sohn writes *pota* and *te*.

## References

* [sohn-1994]
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
