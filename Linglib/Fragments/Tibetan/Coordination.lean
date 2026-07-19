import Linglib.Semantics.Coordination.Defs

/-!
# Classical Tibetan Coordination Morphemes
[beyer-1992] [haspelmath-2007]

Classical Tibetan uses *-daŋ* postpositively on the first coordinand
(monosyndetic A-co B), with diachronic source from the comitative marker
'with'. [haspelmath-2007] (21) cites [beyer-1992]:240.

- *-daŋ* — J, bound, postpositive on first coordinand

Modern Tibetan dialects diverge; this Fragment encodes the Classical form.

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.classicalTibetan`).
-/

namespace Tibetan.Coordination

/-- *-daŋ* — J particle (Classical Tibetan), comitative-derived. Bound,
    postpositive on the first coordinand giving A-co B pattern. -/
def dang : Coordinator :=
  { form := "-daŋ", gloss := "and; with"
  , role := .j, kind := .bound .after .clitic
  , note := "Classical; comitative-derived; medial postpositive on first conjunct" }

def allEntries : List Coordinator := [dang]

end Tibetan.Coordination
