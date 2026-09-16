import Linglib.Syntax.Category.Adposition.Basic
import Linglib.Syntax.Category.Adposition.Order

/-!
# English adpositions

WALS-derived adposition order for English (ISO `eng`), a pass-through of
`Adposition.AdpositionOrder.ofWALS "eng"`, WALS Ch 85 classifying English as prepositional; and
the temporal adpositions that take a measure phrase: *for three hours*, *in three hours* and the
postposition *three days ago*. Which interval the measure applies to, the runtime of an atelic or
telic eventuality ([dowty-1979]'s *for* and *in* tests, `Aspect.forXPrediction` and
`Aspect.inXPrediction`), the offset from the utterance time, or under negation and the perfect the
gap since the last event, is not lexical and is left to the studies; the polarity item *in years* is
`English.PolarityItems.inYears`.

## References

* [dowty-1979]
-/

namespace English

/-- English adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "eng"

namespace Adpositions

/-- *for*, with a measure phrase: *Mary was sick for three hours*. -/
def for_ : Adposition :=
  { form := .simple "for", relation := .temporal, complement := [.measure],
    linearization := [.pre] }

/-- *in*, with a measure phrase: *Mary wrote a paper in three days*, *Mary hasn't been sick in
years*. -/
def in_ : Adposition :=
  { form := .simple "in", relation := .temporal, complement := [.measure],
    linearization := [.pre] }

/-- *ago*, the postposition: *Mary left three days ago*. -/
def ago : Adposition :=
  { form := .simple "ago", relation := .temporal, complement := [.measure],
    linearization := [.post] }

end Adpositions

end English
