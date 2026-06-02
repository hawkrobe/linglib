import Linglib.Semantics.Evidential.Defs

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

namespace Tuyuca.Evidentiality

/-! ### Typed evidential inventory

Tuyuca's 5-term D1 system per @cite{aikhenvald-2004} Ch 2 §2.4 and
@cite{barnes-1984}. -/

open Semantics.Evidential

/-- Tuyuca evidential inventory in the new typed form. Five entries:
    two `Direct` (visual/non-visual sensory), two `Inferential`
    (from-result/from-assumption), one `Reportative` (unidentified). -/
def evidentials : List Entry :=
  [ .direct      { form := "-wi",   exponent := .verbalAffix, source := .visual },
    .direct      { form := "-ti",   exponent := .verbalAffix, source := .nonvisualSensory },
    .inferential { form := "-yi",   exponent := .verbalAffix, basis  := .fromResult },
    .reportative { form := "-yigi", exponent := .verbalAffix, sourceIdentity := .unidentified },
    .inferential { form := "-hiyi", exponent := .verbalAffix, basis  := .fromAssumption } ]

/-! Structural facts about the inventory, decide-checked. -/

example : evidentials.length = 5 := by decide
example : (evidentials.filter Entry.IsDirect).length = 2 := by decide
example : (evidentials.filter Entry.IsReportative).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 2 := by decide

/-- The visual/non-visual sensory distinction is now typed substrate,
    not String literals — provable from the declared inventory. -/
example :
    evidentials.filterMap (fun e => match e with
                                    | .direct d => some d.source
                                    | _ => none) =
    [.visual, .nonvisualSensory] := by decide

/-- The from-result/from-assumption inferential distinction likewise. -/
example :
    evidentials.filterMap (fun e => match e with
                                    | .inferential e => some e.basis
                                    | _ => none) =
    [.fromResult, .fromAssumption] := by decide

end Tuyuca.Evidentiality
