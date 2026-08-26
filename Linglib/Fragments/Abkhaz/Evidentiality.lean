import Linglib.Semantics.Evidential.Defs

/-!
# Abkhaz evidentiality

Abkhaz has a two-choice system of Aikhenvald's type A2: a dedicated, tense-neutral
non-firsthand affix (*-zaap'* with present, aorist, perfect and one future; *-zaarən* with
imperfect, past indefinite, pluperfect and one future conditional) covering inference from
results and verbal report, restricted to declarative main clauses.

## References

* [aikhenvald-2004], §2.1
* [de-haan-2013]
-/

namespace Abkhaz.Evidentiality

open Semantics.Evidential

/-- The non-firsthand affixes *-zaap'* and *-zaarən*. -/
def evidentials : List Entry :=
  [ .nonfirsthand { form := "-zaap'/-zaarən", exponent := .verbalAffix } ]

end Abkhaz.Evidentiality
