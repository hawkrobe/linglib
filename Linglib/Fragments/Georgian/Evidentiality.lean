import Linglib.Typology.Modality

/-!
# Georgian Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `directAndIndirect`. @cite{aikhenvald-2004}
analyzes Georgian's evidential perfect ("I screeve") as marking inference
or report only — `indirectOnly`. Studies-side override.
-/

namespace Georgian.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Georgian evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Georgian" "kat" "Kartvelian"
    (markers := ["evidential perfect (I screeve)"])
    (notes := "Evidential perfect for inference/report; fused with tense-aspect " ++
              "screeve system")
    (attestedEvidentials := [.inference, .hearsay])
    (systemFb := .indirectOnly)
    (codingFb := .partOfTAM)

example : evidentialityProfile.iso = "kat" ∧ evidentialityProfile.language = "Georgian" :=
  ⟨rfl, rfl⟩

end Georgian.Evidentiality
