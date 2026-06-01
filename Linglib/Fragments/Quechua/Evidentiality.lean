import Linglib.Typology.Modality

/-!
# Quechua (Cuzco) Evidentiality
@cite{aikhenvald-2004}

Three-or-more system: direct *-mi*, reportative *-si*, conjectural *-chá*.
Obligatory enclitics on finite clauses. Canonical Andean evidential system.
WALS Ch 77 has no entry for Cuzco Quechua (`quz`); the fallback fires.

The local `EvidentialSystem` enum extends WALS Ch 77's 3-way to a 4-way
by adding `threeOrMore` precisely to capture this Andean pattern.
-/

namespace Quechua.Evidentiality

open Typology.Modality
open Features.Evidentiality (EvidentialSource)

/-- Cuzco Quechua evidentiality: canonical 3-way Andean system. -/
def evidentialityProfile : EvidentialityProfile :=
  .fromWALS "Quechua (Cuzco)" "quz" "Quechuan"
    (markers := ["-mi (direct)", "-si (reportative)", "-chá (conjectural)"])
    (notes := "Canonical three-way system: direct/reportative/conjectural; " ++
              "obligatory on finite clauses")
    (attestedEvidentials := [.direct, .hearsay, .inference])
    (systemFb := .threeOrMore)
    (codingFb := .verbalAffix)

example : evidentialityProfile.iso = "quz" ∧
    evidentialityProfile.language = "Quechua (Cuzco)" := ⟨rfl, rfl⟩

end Quechua.Evidentiality
