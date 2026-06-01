import Linglib.Typology.Modality

/-!
# Abkhaz Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (verbal-affix coding).
@cite{aikhenvald-2004} analyzes Abkhaz as 2-way direct/indirect (fused with
TAM). Studies-side override.
-/

namespace Abkhaz.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Abkhaz evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Abkhaz" "abk" "Northwest Caucasian"
    (markers := ["finite verb (direct)", "nonfinite + copula (indirect)"])
    (notes := "Caucasus areal feature; classified differently by WALS vs Aikhenvald")
    (attestedEvidentials := [.direct, .inference])
    (systemFb := .directAndIndirect)
    (codingFb := .partOfTAM)

example : evidentialityProfile.iso = "abk" ∧ evidentialityProfile.language = "Abkhaz" :=
  ⟨rfl, rfl⟩

end Abkhaz.Evidentiality
