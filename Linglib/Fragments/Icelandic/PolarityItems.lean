import Linglib.Semantics.Polarity.Licensing
import Linglib.Fragments.Icelandic.TemporalConnectives

/-!
# Icelandic polarity items

Polarity items of Icelandic typed by `Polarity.Item`: *fyrr en*, literally 'earlier than', the
punctual *until* that needs the negation *ekki* ([giannakidou-2002], the paper's (46), from
Gunnar Hansson).

## References

* [giannakidou-2002]
-/

namespace Icelandic.PolarityItems

open Polarity

/-- *fyrr en*, the punctual *until*, licensed by negation. Its connective entry is
`Icelandic.TemporalConnectives.fyrrEn`. -/
def fyrrEn : Item :=
  { form := TemporalConnectives.fyrrEn.form
  , licensor := some .antiAdditive
  , baseForce := .temporal
  , licensingContexts := [.negation] }

end Icelandic.PolarityItems
