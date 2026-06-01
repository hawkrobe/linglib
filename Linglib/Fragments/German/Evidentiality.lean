import Linglib.Typology.Modality

/-!
# German Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan counts modal verbs
*sollen* / *wollen* as grammatical reportatives). @cite{aikhenvald-2004}'s
stricter criterion treats German as having no grammatical evidentials;
Studies-side override in `Studies/Aikhenvald2004.lean`.
-/

namespace German.Evidentiality

open Typology.Modality

/-- German evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "German" "deu" "Indo-European"
    (notes := "sollen/wollen have evidential uses but are modal verbs")

example : evidentialityProfile.iso = "deu" ∧ evidentialityProfile.language = "German" :=
  ⟨rfl, rfl⟩

end German.Evidentiality
