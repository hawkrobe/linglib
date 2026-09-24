module

public import Linglib.Semantics.Evidential.Defs

/-!
# Mandarin evidentiality

This file records that Mandarin has no grammatical evidentials, as de Haan's survey codes it
(`Data/WALS/Features/F77A.lean`).

## References

* [de-haan-2013]
-/

@[expose] public section

namespace Mandarin.Evidentiality

/-- Mandarin has no evidentials. -/
def evidentials : List Evidential := []

end Mandarin.Evidentiality
