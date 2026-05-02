import Linglib.Typology.Modality

/-!
# Finnish Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan counts modal verbs
as grammatical evidentials). @cite{aikhenvald-2004} treats Finnish as having
no grammatical evidentials; modality via modal verbs (*voida* 'can',
*täytyä* 'must', *saattaa* 'may'). Studies-side override.
-/

namespace Fragments.Finnish.Evidentiality

open Typology.Modality

/-- Finnish evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Finnish" "fin" "Uralic"
    (notes := "No grammatical evidentials per Aikhenvald; modality via modal " ++
              "verbs (voida 'can', täytyä 'must', saattaa 'may')")

example : evidentialityProfile.iso = "fin" ∧ evidentialityProfile.language = "Finnish" :=
  ⟨rfl, rfl⟩

end Fragments.Finnish.Evidentiality
