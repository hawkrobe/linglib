import Linglib.Typology.Modality

/-!
# Turkish Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

Two-choice direct vs indirect. Past-tense paradigm contrasts *-DI*
(witnessed) with *-mIş* (inferred or reported). The canonical
indirect-evidential of a major language. Fused with TAM. WALS and
Aikhenvald agree.
-/

namespace Turkish.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Turkish evidentiality: 2-way direct/indirect, fused with past tense. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Turkish" "tur" "Turkic"
    (markers := ["-DI (direct)", "-mIş (indirect)"])
    (notes := "Evidential distinction fused with past tense; -DI = witnessed, " ++
              "-mIş = inferred/reported")
    (attestedEvidentials := [.direct, .inference, .hearsay])
    (systemFb := .directAndIndirect)
    (codingFb := .partOfTAM)

example : evidentialityProfile.iso = "tur" ∧ evidentialityProfile.language = "Turkish" :=
  ⟨rfl, rfl⟩

end Turkish.Evidentiality
