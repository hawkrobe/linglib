import Linglib.Typology.Modality

/-!
# Korean Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `indirectOnly` (de Haan counts *-deo-*
retrospective as grammatical evidential). @cite{aikhenvald-2004} treats it
as not classified as grammatical evidential; Studies-side override.
-/

namespace Fragments.Korean.Evidentiality

open Typology.Modality

/-- Korean evidentiality typology per WALS @cite{de-haan-2013}. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Korean" "kor" "Koreanic"
    (notes := "-deo- (retrospective) has evidential-like function; classified " ++
              "differently by WALS vs Aikhenvald")

example : evidentialityProfile.iso = "kor" ∧ evidentialityProfile.language = "Korean" :=
  ⟨rfl, rfl⟩

end Fragments.Korean.Evidentiality
