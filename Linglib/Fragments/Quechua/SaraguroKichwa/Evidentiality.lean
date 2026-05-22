import Linglib.Typology.Modality

/-!
# Saraguro Kichwa Evidentiality
@cite{aikhenvald-2004} @cite{martinez-vera-2026}

Saraguro Kichwa (ISO `qvj`) is a severely endangered Quechuan language
spoken in the Saraguro region of Loja Province, Ecuador
(@cite{martinez-vera-2026}).

The evidential paradigm has a 3-way distinction in matrix declaratives:

* `-rka`  — direct (also past tense)
* `-shka` — reportative (also past tense)
* `-shi`  — inferential

Plus the discourse-sensitive enclitic `=mi`, whose semantic analysis is
contested across Quechuan varieties (Faller's direct-evidential analysis
for Cuzco Quechua does NOT carry over to Saraguro per
@cite{martinez-vera-2026}). The Fragment records only the consensus
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

namespace Fragments.Quechua.SaraguroKichwa.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Saraguro Kichwa evidentiality: 3-way Andean system in matrix
    declaratives.

    The `=mi` enclitic is intentionally NOT listed under `markers`: per
    @cite{martinez-vera-2026}, `=mi` is a focus marker (with verum and
    contrastive uses) sensitive to the QUD, not an evidential per se.
    The earlier Faller (2002) tradition treating Cuzco `=mi` as the
    direct evidential does not extend to Saraguro Kichwa. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Saraguro Kichwa" "qvj" "Quechuan"
    (markers := ["-rka (direct)", "-shka (reportative)", "-shi (inferential)"])
    (notes := "Three-way evidential paradigm in matrix declaratives. " ++
              "The discourse-sensitive enclitic =mi (focus + verum, " ++
              "@cite{martinez-vera-2026}) is NOT listed here as it is " ++
              "not analysed as an evidential in this variety.")
    (attestedEvidentials := [.direct, .hearsay, .inference])
    (systemFb := .threeOrMore)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "qvj" ∧
    evidentialityProfile.language = "Saraguro Kichwa" := ⟨rfl, rfl⟩

end Fragments.Quechua.SaraguroKichwa.Evidentiality
