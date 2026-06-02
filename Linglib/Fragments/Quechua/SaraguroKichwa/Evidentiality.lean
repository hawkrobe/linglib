import Linglib.Semantics.Evidential.Defs

/-!
# Saraguro Kichwa Evidentiality
[aikhenvald-2004] [martinez-vera-2026]

Saraguro Kichwa (ISO `qvj`) is a severely endangered Quechuan language
spoken in the Saraguro region of Loja Province, Ecuador
([martinez-vera-2026]).

The evidential paradigm has a 3-way distinction in matrix declaratives:

* `-rka`  — direct (also past tense)
* `-shka` — reportative (also past tense)
* `-shi`  — inferential

Plus the discourse-sensitive enclitic `=mi`, whose semantic analysis is
contested across Quechuan varieties (Faller's direct-evidential analysis
for Cuzco Quechua does NOT carry over to Saraguro per
[martinez-vera-2026]). The Fragment records only the consensus
typological metadata; the focus-marker-with-discourse-sensitivity
analysis lives in `Studies/MartinezVera2026.lean`.

WALS Ch 77 has no entry for `qvj`; the `threeOrMore` fallback fires.

## Family-style organisation

This file sits as `Fragments/Quechua/SaraguroKichwa/` mirroring the
`Fragments/Slavic/{Bulgarian,Czech,Russian,...}/` precedent for
intra-family disambiguation. The `Fragments/Quechua/` files at the same
level are currently misnamed (some claim `quz` Cuzco, one claims `qvi`
Imbabura) and are queued for a separate per-variety restructure; this
file does not touch them.
-/

namespace Quechua.SaraguroKichwa.Evidentiality

/-! ### Typed evidential inventory

Saraguro Kichwa's 3-way matrix-declarative system per
[martinez-vera-2026]: direct `-rka`, reportative `-shka`,
inferential `-shi`. The focus-and-verum enclitic `=mi` is intentionally
excluded (not analyzed as an evidential in this variety). -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "-rka",  exponent := .verbalAffix },
    .reportative { form := "-shka", exponent := .verbalAffix,
                   sourceIdentity := .unidentified },
    .inferential { form := "-shi",  exponent := .verbalAffix } ]

example : evidentials.length = 3 := by decide
example : (evidentials.filter Entry.IsDirect).length = 1 := by decide
example : (evidentials.filter Entry.IsReportative).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end Quechua.SaraguroKichwa.Evidentiality
