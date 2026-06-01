import Linglib.Typology.Modality

/-!
# Kashaya Evidentiality
@cite{aikhenvald-2004} @cite{oswalt-1986} @cite{de-haan-2013}

Five-term system distinguishing visual from auditory direct evidence.
WALS @cite{de-haan-2013} F77A codes Kashaya as `directAndIndirect`;
@cite{aikhenvald-2004} (citing @cite{oswalt-1986}) recognizes the richer
4-or-5-way distinction. Studies-side override per Aikhenvald.
-/

namespace Kashaya.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Kashaya evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Kashaya" "kju" "Pomoan"
    (markers := ["-ya (performative)", "-ʔ (visual)", "-inne (auditory)",
                 "-qa (inferential)", "-do (reportative)"])
    (notes := "Four-way sensory+inferential+reportative; distinguishes " ++
              "visual from auditory direct evidence; Oswalt (1986)")
    (attestedEvidentials := [.direct, .hearsay, .inference])
    (systemFb := .threeOrMore)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "kju" ∧ evidentialityProfile.language = "Kashaya" :=
  ⟨rfl, rfl⟩

end Kashaya.Evidentiality
