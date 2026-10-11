module

public import Linglib.Semantics.Evidential.Defs

/-!
# Tariana evidentiality

Tariana (Arawak, Vaupés) has a five-choice system of Aikhenvald's type D1, fused with tense:
in the recent past, visual *-ka*, non-visual sensory *-mha*, inferred *-nihka*, assumed
*-sika* and reported *-pidaka*. WALS codes the language as having direct and indirect
evidentials.

## References

* [aikhenvald-2004], §2.4
* [de-haan-2013]
-/

@[expose] public section

namespace Tariana.Evidentiality

open Evidential

/-- The recent-past forms: visual, non-visual, inferred, assumed and reported. -/
def evidentials : List Evidential :=
  [ { morphs := [.suff "ka"], exponent := .verbalAffix, covers := {.visual} },
    { morphs := [.suff "mha"], exponent := .verbalAffix, covers := {.sensory} },
    { morphs := [.suff "nihka"], exponent := .verbalAffix, covers := {.inference} },
    { morphs := [.suff "sika"], exponent := .verbalAffix, covers := {.assumption} },
    { morphs := [.suff "pidaka"], exponent := .verbalAffix, covers := {.hearsay} } ]

end Tariana.Evidentiality
