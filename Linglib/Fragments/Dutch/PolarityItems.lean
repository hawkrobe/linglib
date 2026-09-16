import Linglib.Semantics.Polarity.Licensing
import Linglib.Fragments.Dutch.TemporalConnectives

/-!
# Dutch polarity items

Polarity items of Dutch typed by `Polarity.Item`: *pas* 'only then', the positive polarity item
that serves as the punctual *until* and does not combine with negation ([giannakidou-2002], the
paper's (47); [karttunen-1974] on the parallel German *erst*).

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

namespace Dutch.PolarityItems

open Polarity

/-- *pas*, the punctual *until* of a positive clause. Its connective entry is
`Dutch.TemporalConnectives.pas`. -/
def pas : Item :=
  { form := TemporalConnectives.pas.form
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

end Dutch.PolarityItems
