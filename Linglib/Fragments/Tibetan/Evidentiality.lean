import Linglib.Semantics.Evidential.Defs

/-!
# Tibetan (Lhasa) evidentiality

Lhasa (Standard) Tibetan marks evidentiality in its final auxiliaries, fused with aspect, and
[tournadre-lapolla-2014] read the system as marking two things: the speaker's *access* to the
information and its *source*. In the perfective, sensory *-song* marks an event the speaker
perceived through any of the senses, *-bzhag* one inferred from direct knowledge of its
result, and factual *-pa red* one known from reasoning or general knowledge, which
[delancey-2001] glosses indirect; the hearsay suffix *-za* marks source alone and can follow
any of them. The copulas and imperfective auxiliaries carry the same access contrast
(*'dug* is the present counterpart of *-song*, *yod-red* of *-pa red*), so a term's form is
given here in the perfective. Aikhenvald, following [delancey-1986]'s description of *-song*
against *-pa red*, reads the perfective as a firsthand ~ non-firsthand system and confines
evidentiality proper to it. The egophoric auxiliaries *-pa yin* and *-byung* and the copulas
*yin* and *yod* mark the speaker's personal knowledge or intention, which is not one of the
six parameters of information source; Aikhenvald lists the *yin* ~ *red*, *yod* ~ *'dug*
opposition, described as conjunct ~ disjunct, among the evidentiality strategies.

## References

* [aikhenvald-2004], §2.1, §4.6
* [delancey-1986]
* [delancey-2001]
* [tournadre-2008]
* [tournadre-lapolla-2014]
-/

namespace Tibetan.Evidentiality

open Evidential

/-- The perfective access markers, sensory *-song*, inferential *-bzhag* and factual
*-pa red*, and the hearsay source marker *-za*. -/
def evidentials : List Evidential :=
  [ { form := "-song", exponent := .tamFusion, covers := {.visual, .sensory} },
    { form := "-bzhag", exponent := .tamFusion, covers := {.inference} },
    { form := "-pa red", exponent := .tamFusion, covers := {.assumption} },
    { form := "-za", exponent := .verbalAffix, covers := {.hearsay} } ]

end Tibetan.Evidentiality
