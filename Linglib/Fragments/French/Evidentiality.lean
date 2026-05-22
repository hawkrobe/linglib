import Linglib.Typology.Modality

/-!
# French Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan codes the conditional
as a grammatical reportative). @cite{aikhenvald-2004}'s stricter criterion
treats French as having no grammatical evidentials; Studies-side override
in `Studies/Aikhenvald2004.lean`.
-/

namespace Fragments.French.Evidentiality

open Typology.Modality

/-- French evidentiality typology per WALS @cite{de-haan-2013}: indirect-only
    via the journalistic-conditional reportative use. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "French" "fra" "Indo-European"
    (notes := "Conditional has secondary reportative use in journalistic register")

example : evidentialityProfile.iso = "fra" ∧ evidentialityProfile.language = "French" :=
  ⟨rfl, rfl⟩

end Fragments.French.Evidentiality
