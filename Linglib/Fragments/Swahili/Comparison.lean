module

public import Linglib.Syntax.Comparative

/-!
# Swahili comparison

This file defines the Swahili comparative construction. Stassen codes Swahili in the World
Atlas of Language Structures as an exceed comparative: the standard of comparison is the
object of *kuliko*, a verb-derived marker, as in *X ni Adj kuliko Y*, and the adjective carries
no degree marking. The construction's anatomy is stated so that its type, read off the
anatomy, is the type the atlas records.

## Main definitions

* `Swahili.Comparison.kuliko`: the comparative construction

## Main results

* `Swahili.Comparison.type_kuliko`, `Swahili.Comparison.type_eq_wals`: the construction is an
  exceed comparative, as the atlas codes Swahili

## Implementation notes

* The atlas datapoint cites Ashton's grammar, which was not opened; the marker and the
  absence of degree marking are recorded as the datapoint's type implies them and await the
  grammar for the verbal *-zidi* variant and the superlative.

## References

* [L. Stassen, *Comparative Constructions* (2013)][stassen-2013]
-/

@[expose] public section

namespace Swahili.Comparison

open Comparative

/-- The *kuliko* comparative, whose standard is the object of the marker and whose adjective
is unmarked for degree. -/
def kuliko : Comparative :=
  { standardMarker := some "kuliko", caseAssignment := .fixed, fixedEncoding := some .directObject }

/-- The construction is an exceed comparative. -/
theorem type_kuliko : kuliko.type = .exceed := rfl

/-- The atlas codes Swahili as the construction's type. -/
theorem type_eq_wals : ComparativeType.ofWALS "swh" = some kuliko.type := by decide

end Swahili.Comparison
