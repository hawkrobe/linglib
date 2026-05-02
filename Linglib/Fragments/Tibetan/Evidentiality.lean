import Linglib.Typology.Modality

/-!
# Tibetan (Lhasa) Evidentiality
@cite{aikhenvald-2004}

Two-choice direct vs indirect via copula/auxiliary contrast. *red*/*yod*
(personal knowledge) vs *yin*/*'dug* (indirect or new information).
Egophoric system. WALS Ch 77 has no entry; the fallback fires.
-/

namespace Fragments.Tibetan.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Tibetan (Lhasa) evidentiality: 2-way egophoric system via copula contrast. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Tibetan (Lhasa)" "bod" "Sino-Tibetan"
    (markers := ["red (direct)", "'dug (indirect)", "yod (direct)", "yin (indirect)"])
    (notes := "Egophoric system; direct/personal knowledge vs indirect/new info; " ++
              "expressed via copula and auxiliary contrasts")
    (attestedEvidentials := [.direct, .inference])
    (systemFb := .directAndIndirect)
    (codingFb := .particle)

example : evidentialityProfile.iso = "bod" ∧
    evidentialityProfile.language = "Tibetan (Lhasa)" := ⟨rfl, rfl⟩

end Fragments.Tibetan.Evidentiality
