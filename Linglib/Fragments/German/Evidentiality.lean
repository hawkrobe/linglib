module

public import Linglib.Semantics.Evidential.Defs

/-!
# German evidentiality

This file records that German has no grammatical evidentials. Aikhenvald counts the present
conditional, Konjunktiv I, which marks reported speech and can stand on its own in free indirect
speech, as an evidentiality strategy rather than an evidential, and she discusses the modal verb
*sollen*, which can mark information as reported or inferred, as a candidate strategy whose
status turns on whether the modals are a closed class. De Haan's survey instead codes German as
having indirect evidentials only (`Data/WALS/Features/F77A.lean`), which WALS Feature 78A codes
as a modal morpheme, so the two classifications differ over the modals.

## References

* [aikhenvald-2004]
* [de-haan-2013]
-/

@[expose] public section

namespace German.Evidentiality

/-- German has no evidentials. -/
def evidentials : List Evidential := []

end German.Evidentiality
