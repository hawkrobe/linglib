import Linglib.Typology.Modality

/-!
# Mandarin Chinese Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `noGrammaticalEvidentials`. Lexical
strategies: *tinshuo* (听说), *juede* (觉得), sentence-final *ba* (吧).
-/

namespace Fragments.Mandarin.Evidentiality

open Typology.Modality

/-- Mandarin evidentiality typology per WALS: no grammatical evidentials. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Mandarin" "cmn" "Sino-Tibetan"
    (notes := "Lexical evidential strategies: tinshuo, juede; no obligatory marking")

example : evidentialityProfile.iso = "cmn" ∧ evidentialityProfile.language = "Mandarin" :=
  ⟨rfl, rfl⟩

end Fragments.Mandarin.Evidentiality
