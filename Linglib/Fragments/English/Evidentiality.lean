import Linglib.Typology.Modality

/-!
# English Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

WALS @cite{de-haan-2013} F77A: `noGrammaticalEvidentials`. Evidential source
is conveyed lexically by adverbs ("apparently", "reportedly") or hedging
expressions, never by obligatory verbal morphology.
-/

namespace English.Evidentiality

open Typology.Modality

/-- English evidentiality typology per WALS: no grammatical evidentials. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "English" "eng" "Indo-European"
    (notes := "Lexical evidentials only: apparently, reportedly, evidently")

example : evidentialityProfile.iso = "eng" ∧ evidentialityProfile.language = "English" :=
  ⟨rfl, rfl⟩

end English.Evidentiality
