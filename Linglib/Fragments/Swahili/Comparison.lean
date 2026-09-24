module

public import Linglib.Syntax.Comparative

/-!
# Swahili comparison

This file defines the Swahili comparative construction as Stassen's atlas entry records it,
from Ashton's grammar. The standard of comparison is the object of *kuliko*, a verb-derived
marker, as in *X ni Adj kuliko Y*, and the adjective carries no degree marking, so the
construction's type, read off its anatomy, is the exceed comparative.

## Main definitions

* `Swahili.Comparison.kuliko`: the comparative construction

## Main results

* `Swahili.Comparison.type_kuliko`: the construction is an exceed comparative

## Implementation notes

* Ashton's grammar was not opened; the marker and the absence of degree marking are recorded
  as the atlas entry's type implies them and await the grammar for the verbal *-zidi* variant
  and the superlative.

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


end Swahili.Comparison
