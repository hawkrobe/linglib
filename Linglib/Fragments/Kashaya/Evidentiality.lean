import Linglib.Semantics.Evidential.Defs

/-!
# Kashaya Evidentiality
@cite{aikhenvald-2004} @cite{oswalt-1986} @cite{de-haan-2013}

@cite{oswalt-1986} organizes the Kashaya evidential suffixes into a
five-level hierarchy:

    Performative > Factual-Visual > Auditory > Inferential > Quotative

Performative `-wela`/`-mela` (imperfective/perfective) sits at the top:
the speaker performs or has just performed the act. Factual `-wâ` and
Visual `-yá` form a single hierarchical level split by aspect — factual
also covers generic common knowledge. Auditory `-V̂nnâ` marks non-visual
sensory evidence; the auditory/visual split is what makes Kashaya
famous in the typological literature (@cite{aikhenvald-2004}).
Inferential I `-qá` is the default non-sensory inference; a distinct
Inferential II `-bi` heads subordinate clauses. Quotative `-do` marks
hearsay. In the narrative mode, the direct-evidence distinctions
collapse to Personal Experience `-yowâ` and (archaic) Remote Past
`-miyâ`.

WALS @cite{de-haan-2013} F77A codes Kashaya (kju) as `directAndIndirect`
(value 3). The five-level hierarchy is preserved in the `markers` field.
-/

namespace Kashaya.Evidentiality

/-! ### Typed evidential inventory

Oswalt's five-level hierarchy (@cite{oswalt-1986}) collapsed onto the
substrate trichotomy: performative + factual-visual + auditory map to
`Direct`; inferential I and II to `Inferential`; quotative to
`Reportative`. The auditory/visual contrast — Kashaya's typologically
famous feature — is preserved as `DirectSource.auditory` vs `.visual`. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "-wela/-mela", exponent := .verbalAffix },
    .direct      { form := "-wâ/-yá",     exponent := .verbalAffix, source := .visual },
    .direct      { form := "-V̂nnâ",       exponent := .verbalAffix, source := .auditory },
    .inferential { form := "-qá",         exponent := .verbalAffix },
    .inferential { form := "-bi",         exponent := .verbalAffix },
    .reportative { form := "-do",         exponent := .verbalAffix,
                   sourceIdentity := .identified } ]

example : evidentials.length = 6 := by decide
example : (evidentials.filter Entry.IsDirect).length = 3 := by decide
example : (evidentials.filter Entry.IsReportative).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 2 := by decide

/-- The auditory/visual split for Kashaya direct evidentials —
    typologically rare, now typed. -/
example :
    evidentials.filterMap (fun e => match e with
                                    | .direct d => some d.source
                                    | _ => none) =
    [.unspecified, .visual, .auditory] := by decide

end Kashaya.Evidentiality
