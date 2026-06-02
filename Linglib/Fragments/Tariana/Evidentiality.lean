import Linglib.Semantics.Evidential.Defs

/-!
# Tariana Evidentiality
@cite{aikhenvald-2004} @cite{de-haan-2013}

Five-term system in the Vaupés multilingual area: visual, nonvisual,
inferred, assumed, reported. WALS @cite{de-haan-2013} F77A codes Tariana as
`directAndIndirect`; @cite{aikhenvald-2004}'s richer typology distinguishes
the 5-way system. Studies-side override.
-/

namespace Tariana.Evidentiality

/-! ### Typed evidential inventory

Tariana's classic D1 5-term Vaupés system per @cite{aikhenvald-2004}:
visual, non-visual sensory, inferred (from result), assumed (from
reasoning), reported. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "-ka",     exponent := .verbalAffix, source := .visual },
    .direct      { form := "-mha",    exponent := .verbalAffix, source := .nonvisualSensory },
    .inferential { form := "-nihka",  exponent := .verbalAffix, basis  := .fromResult },
    .inferential { form := "-sika",   exponent := .verbalAffix, basis  := .fromAssumption },
    .reportative { form := "-pidaka", exponent := .verbalAffix,
                   sourceIdentity := .unidentified } ]

example : evidentials.length = 5 := by decide
example : (evidentials.filter Entry.IsDirect).length = 2 := by decide
example : (evidentials.filter Entry.IsReportative).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 2 := by decide

/-- D1 visual/non-visual distinction provable from typed data. -/
example :
    evidentials.filterMap (fun e => match e with
                                    | .direct d => some d.source
                                    | _ => none) =
    [.visual, .nonvisualSensory] := by decide

end Tariana.Evidentiality
