import Linglib.Semantics.Evidential.Defs

/-!
# Bulgarian evidentiality

Bulgarian marks non-firsthand information with the *l*-form, fused with tense and aspect,
which covers inference and report and carries epistemic overtones of distance; the aorist is
the unmarked counterpart. Aikhenvald classes the system as possibly A2, while noting that
Balkan Slavic has been drifting toward an A1 system in which the unmarked form comes to signal
firsthand information. The [cumming-2026] tense-evidential paradigm data are in
`Fragments/Slavic/Bulgarian/Evidentials.lean`.

## References

* [aikhenvald-2004], §2.1, §4.8
* [de-haan-2013]
-/

namespace Bulgarian.Evidentiality

open Semantics.Evidential

/-- The non-firsthand *l*-form; the aorist is its unmarked counterpart. -/
def evidentials : List Evidential :=
  [ { form := "l-form", exponent := .tamFusion, covers := {.inference, .assumption, .hearsay} } ]

end Bulgarian.Evidentiality
