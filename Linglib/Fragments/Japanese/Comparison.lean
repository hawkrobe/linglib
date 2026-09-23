module

public import Linglib.Syntax.Comparative

/-!
# Japanese comparison

Japanese compares with the standard marked by the postposition *yori* 'from, than', the
ablative of the literary language, and the adjective in its bare form: *Tarō wa Hanako yori se
ga takai* 'Taro is taller than Hanako'. It is a separative comparative in Stassen's typology,
its marker taken from spatial case, and the superlative is the comparative with a universal
standard, *dare yori mo* 'than anyone'.

## References

* [stassen-1985]
-/

@[expose] public section

namespace Japanese.Comparison

open Comparative

/-- The *yori*-comparative: separative (ablative) postposition-marked
    standard, no degree morphology. -/
def yori : Comparative :=
  { standardMarker := some "yori"
  , caseAssignment := .fixed
  , fixedEncoding := some .adverbial
  , standardCase := some .abl }

/-- No overt degree marking. -/
def degreeWord : DegreeWordType := .noDegreeMarking

/-- Superlative as comparative with universal standard (*dare yori mo*). -/
def superlative : SuperlativeStrategy := .comparativeUniversal

end Japanese.Comparison
