import Linglib.Semantics.Evidential.Defs

/-!
# Tibetan (Lhasa) evidentiality

Lhasa Tibetan marks information source in its final auxiliaries, fused with aspect, and
Aikhenvald confines its evidentiality proper to the perfective. There *-song* marks an event
the speaker perceived, *-bzhag* an event inferred from direct knowledge of its result, and
*-pa red* one the speaker knows only by report, reasoning or general knowledge, which
[delancey-2001] glosses indirect and [tournadre-2008] factual; Aikhenvald reads the system
as firsthand ~ non-firsthand, [delancey-1986] having described *-song* against *-pa red*
alone. A quotative *-za* may follow any of the three, shifting the information access to a
quoted speaker, and the remaining perfective auxiliaries *-pa yin* and *-byung* track the
speaker's volition and involvement rather than source. So does the copular opposition
*yin* ~ *red* (equational) and *yod* ~ *'dug* (existential), described as conjunct ~ disjunct
and later as egophoric, which Aikhenvald lists among the evidentiality strategies; neither is
in the inventory.

## References

* [aikhenvald-2004], §2.1, §4.6
* [delancey-1986]
* [delancey-2001]
* [tournadre-2008]
-/

namespace Tibetan.Evidentiality

open Evidential

/-- The perfective evidentials: sensory *-song*, inferential *-bzhag* and factual *-pa red*. -/
def evidentials : List Evidential :=
  [ { form := "-song", exponent := .tamFusion, covers := {.visual, .sensory} },
    { form := "-bzhag", exponent := .tamFusion, covers := {.inference} },
    { form := "-pa red", exponent := .tamFusion, covers := {.assumption, .hearsay} } ]

end Tibetan.Evidentiality
