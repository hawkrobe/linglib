import Linglib.Typology.Modality

/-!
# Tuyuca Evidentiality
@cite{aikhenvald-2004} @cite{barnes-1984} @cite{de-haan-2013}

Five-term system: visual, nonvisual, apparent (inferential), secondhand
(reported), assumed. Obligatory verbal suffixes. @cite{barnes-1984} is the
classic description. Vaupés multilingual area.

WALS @cite{de-haan-2013} F77A codes Tuyuca as `directAndIndirect`, lumping
the 5-term system into the canonical 2-way bucket. @cite{aikhenvald-2004}'s
richer typology distinguishes 3-or-more systems; the local `EvidentialSystem`
enum's `threeOrMore` value is the per-Aikhenvald override (Studies-side).
The `markers` field below preserves the full 5-term inventory.
-/

namespace Fragments.Tuyuca.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Tuyuca evidentiality typology per WALS @cite{de-haan-2013}: 2-way
    `directAndIndirect`. The 5-term Aikhenvald analysis is a Studies override. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Tuyuca" "tue" "Tucanoan"
    (markers := ["-wi (visual)", "-ti (nonvisual)", "-yi (apparent)",
                 "-yigi (secondhand)", "-hiyi (assumed)"])
    (notes := "Five-way evidential system per Barnes (1984); WALS lumps " ++
              "into directAndIndirect, Aikhenvald 2004 distinguishes")
    (attestedEvidentials := [.direct, .hearsay, .inference])
    (systemFb := .directAndIndirect)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "tue" ∧ evidentialityProfile.language = "Tuyuca" :=
  ⟨rfl, rfl⟩

end Fragments.Tuyuca.Evidentiality
