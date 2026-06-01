import Linglib.Typology.Modality

/-!
# Aymara Evidentiality
@cite{aikhenvald-2004}

Three-or-more system: direct, reportative, non-personal/inferential. Andean
areal feature shared with Quechua. WALS Ch 77 has no entry; fallback fires.
-/

namespace Aymara.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Aymara evidentiality: 3-way Andean system, parallel to Quechua. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Aymara" "aym" "Aymaran"
    (markers := ["-wa (direct)", "-sa (reportative)", "-pacha (inferential)"])
    (notes := "Obligatory three-way system; Andean areal feature shared with Quechua")
    (attestedEvidentials := [.direct, .hearsay, .inference])
    (systemFb := .threeOrMore)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "aym" ∧ evidentialityProfile.language = "Aymara" :=
  ⟨rfl, rfl⟩

end Aymara.Evidentiality
