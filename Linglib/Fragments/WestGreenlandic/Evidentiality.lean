import Linglib.Typology.Modality

/-!
# West Greenlandic Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

Inferential mood via verbal suffix; no dedicated direct-evidence marker.
WALS and Aikhenvald agree.
-/

namespace Fragments.WestGreenlandic.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- West Greenlandic evidentiality: inferential mood only. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "West Greenlandic" "kal" "Eskimo-Aleut"
    (markers := ["-gunarpoq (inferential mood)"])
    (notes := "Inferential mood only; no dedicated direct marker")
    (attestedEvidentials := [.inference])
    (systemFb := .indirectOnly)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "kal" ∧
    evidentialityProfile.language = "West Greenlandic" := ⟨rfl, rfl⟩

end Fragments.WestGreenlandic.Evidentiality
