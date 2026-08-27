import Linglib.Semantics.Evidential.Defs

/-!
# Kashaya Evidentiality
[aikhenvald-2004] [oswalt-1986] [de-haan-2013]

[oswalt-1986] organizes the Kashaya evidential suffixes into a
five-level hierarchy:

    Performative > Factual-Visual > Auditory > Inferential > Quotative

Performative `-wela`/`-mela` (imperfective/perfective) sits at the top:
the speaker performs or has just performed the act. Factual `-wâ` and
Visual `-yá` form a single hierarchical level split by aspect — factual
also covers generic common knowledge. Auditory `-V̂nnâ` marks non-visual
sensory evidence; the auditory/visual split is what makes Kashaya
famous in the typological literature ([aikhenvald-2004]).
Inferential I `-qá` is the default non-sensory inference; a distinct
Inferential II `-bi` heads subordinate clauses. Quotative `-do` marks
hearsay. In the narrative mode, the direct-evidence distinctions
collapse to Personal Experience `-yowâ` and (archaic) Remote Past
`-miyâ`.

WALS [de-haan-2013] F77A codes Kashaya (kju) as `directAndIndirect`
(value 3). The five-level hierarchy is preserved in the `markers` field.
-/

namespace Kashaya.Evidentiality

/-! ### Typed evidential inventory

Oswalt's five-level hierarchy ([oswalt-1986]) collapsed onto the
substrate trichotomy: performative + factual-visual + auditory map to
`Direct`; inferential I and II to `Inferential`; quotative to
`Reportative`. The auditory/visual contrast — Kashaya's typologically
famous feature — is the visual and sensory terms. The performative and the
    narrative personal-experience and remote-past forms lie outside the six
    parameters of information source; the performative is kept with an empty
    coverage, so the paradigm fits none of Aikhenvald's kinds. -/

open Evidential

def evidentials : List Evidential :=
  [ { form := "-wela/-mela", exponent := .verbalAffix, covers := ∅ },
    { form := "-wâ/-yá", exponent := .verbalAffix, covers := {.visual} },
    { form := "-V̂nnâ", exponent := .verbalAffix, covers := {.sensory} },
    { form := "-qá/-bi", exponent := .verbalAffix, covers := {.inference, .assumption} },
    { form := "-do", exponent := .verbalAffix, covers := {.hearsay} } ]

end Kashaya.Evidentiality
