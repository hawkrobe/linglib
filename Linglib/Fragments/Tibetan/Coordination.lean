import Linglib.Features.Coordination

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

open Features.Coordination

/-- *-daŋ* — J particle (Classical Tibetan), comitative-derived. Bound,
    postpositive on the first coordinand giving A-co B pattern. -/
def dang : CoordEntry :=
  { form := "-daŋ", gloss := "and; with"
  , role := .j, boundness := .bound
  , note := "Classical; comitative-derived; medial postpositive on first conjunct" }

def allEntries : List CoordEntry := [dang]

end Tibetan.Coordination
