import Linglib.Typology.Modality

/-!
# Bulgarian Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

Two-choice direct vs indirect via the aorist (direct) vs l-form (indirect)
contrast, fused with TAM. The best-known European language with grammatical
evidentials. Balkan Sprachbund. WALS and Aikhenvald agree.

Sister to `Fragments/Slavic/Bulgarian/Evidentials.lean` which holds the
@cite{cumming-2026} tense-evidential paradigm data.
-/

namespace Bulgarian.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Bulgarian evidentiality: 2-way direct/indirect via aorist vs l-form. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Bulgarian" "bul" "Indo-European"
    (markers := ["aorist (direct)", "l-form (indirect)"])
    (notes := "Balkan evidentiality; direct (aorist) vs indirect (l-participle " ++
              "based forms); fused with tense-aspect")
    (attestedEvidentials := [.direct, .inference, .hearsay])
    (systemFb := .directAndIndirect)
    (codingFb := .partOfTAM)

example : evidentialityProfile.iso = "bul" ∧ evidentialityProfile.language = "Bulgarian" :=
  ⟨rfl, rfl⟩

end Bulgarian.Evidentiality
