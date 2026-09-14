import Linglib.Semantics.Evidential.Defs

/-!
# Kashaya evidentiality

Kashaya (Pomoan) has a complex system that Aikhenvald sets beside the five-choice kind.
[oswalt-1986] arranges its suffixes in a hierarchy of preferred evidentials: performative
*-wela* ~ *-mela* (the speaker performs or has just performed the act; first person only),
factual-visual *-wâ* ~ *-yá* (an imperfective ~ perfective pair, the factual also covering
general knowledge), auditory *-V̂nnâ*, inferential *-qá* (with *-bi* a possible distributional
variant) and quotative *-do*. The performative lies outside the six parameters of information
source and is kept with an empty coverage, so the paradigm fits none of Aikhenvald's kinds;
the narrative personal-experience *-yowâ* and remote-past *-miyâ*, not clearly evidentials, are
omitted. WALS codes the language as having direct and indirect evidentials.

## References

* [aikhenvald-2004], §2.4, §10.2
* [oswalt-1986]
* [de-haan-2013]
-/

namespace Kashaya.Evidentiality

open Evidential

/-- Performative, factual-visual, auditory, inferential and quotative, in Oswalt's order. -/
def evidentials : List Evidential :=
  [ { form := "-wela/-mela", exponent := .verbalAffix, covers := ∅ },
    { form := "-wâ/-yá", exponent := .verbalAffix, covers := {.visual} },
    { form := "-V̂nnâ", exponent := .verbalAffix, covers := {.sensory} },
    { form := "-qá/-bi", exponent := .verbalAffix, covers := {.inference, .assumption} },
    { form := "-do", exponent := .verbalAffix, covers := {.hearsay} } ]

end Kashaya.Evidentiality
