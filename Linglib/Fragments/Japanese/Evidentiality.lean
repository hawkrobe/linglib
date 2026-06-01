import Linglib.Typology.Modality

/-!
# Japanese Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan classifies *soo da*,
*rashii* as grammatical evidentials). @cite{aikhenvald-2004} treats these as
modal rather than evidential; Studies-side override.
-/

namespace Japanese.Evidentiality

open Typology.Modality

/-- Japanese evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Japanese" "jpn" "Japonic"
    (markers := ["soo da", "rashii"])
    (notes := "soo da (hearsay) and rashii (inferential) are modal per Aikhenvald")

example : evidentialityProfile.iso = "jpn" ∧ evidentialityProfile.language = "Japanese" :=
  ⟨rfl, rfl⟩

end Japanese.Evidentiality
