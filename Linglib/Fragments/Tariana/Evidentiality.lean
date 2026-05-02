import Linglib.Typology.Modality

/-!
# Tariana Evidentiality
@cite{aikhenvald-2004} @cite{de-haan-2013}

Five-term system in the Vaupés multilingual area: visual, nonvisual,
inferred, assumed, reported. WALS @cite{de-haan-2013} F77A codes Tariana as
`directAndIndirect`; @cite{aikhenvald-2004}'s richer typology distinguishes
the 5-way system. Studies-side override.
-/

namespace Fragments.Tariana.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Tariana evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Tariana" "tae" "Arawakan"
    (markers := ["-ka (visual)", "-mha (nonvisual)", "-nihka (inferred)",
                 "-sika (assumed)", "-pidaka (reported)"])
    (notes := "Five-way system; Vaupés multilingual area; Aikhenvald (2003, 2004)")
    (attestedEvidentials := [.direct, .hearsay, .inference])
    (systemFb := .threeOrMore)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "tae" ∧ evidentialityProfile.language = "Tariana" :=
  ⟨rfl, rfl⟩

end Fragments.Tariana.Evidentiality
