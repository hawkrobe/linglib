import Linglib.Semantics.Evidential.Defs

/-!
# Tibetan (Lhasa) evidentiality

Lhasa Tibetan marks information source in its copulas and auxiliaries rather than by dedicated
affixes: *red* and *yod* (personal knowledge) contrast with *'dug* and *yin* (indirect or new
information), within an egophoric system.

## References

* [aikhenvald-2004]
-/

namespace Tibetan.Evidentiality

open Evidential

/-- The direct copulas *red* and *yod* and the indirect *'dug* and *yin*. -/
def evidentials : List Evidential :=
  [ { form := "red", exponent := .lexicalFrame, covers := {.visual, .sensory} },
    { form := "yod", exponent := .lexicalFrame, covers := {.visual, .sensory} },
    { form := "'dug", exponent := .lexicalFrame, covers := {.inference, .assumption} },
    { form := "yin", exponent := .lexicalFrame, covers := {.inference, .assumption} } ]

end Tibetan.Evidentiality
