import Linglib.Syntax.Category.Adposition.Basic
import Linglib.Syntax.Category.Adposition.Order

/-!
# English adpositions

WALS-derived adposition order for English (ISO `eng`), a pass-through of
`Adposition.AdpositionOrder.ofWALS "eng"`, WALS Ch 85 classifying English as prepositional; and
the closed-class adpositions as `Adposition` entries: the spatial *to*, *on*, *in*, *into*, *at*,
*from*, *out of* and the particle *out*, the grammatical *by*, *with* and *for*, and the
adpositions that take a measure phrase, *for three hours*, *in three hours* and the postposition
*three days ago*. Which interval
a measure applies to, the runtime of an atelic or telic eventuality ([dowty-1979]'s *for* and *in*
tests, `Aspect.forXPrediction` and `Aspect.inXPrediction`), the offset from the utterance time, or
under negation and the perfect the gap since the last event, is not lexical and is left to the
studies; the polarity item *in years* is `English.PolarityItems.inYears`, the temporal
connectives *before*, *after*, *since*, *until* and *by* are `English.TemporalConnectives`, and the
agent-marking of passive *by* is a study-level refinement.

## References

* [dowty-1979]
-/

namespace English

/-- English adposition order (WALS Ch 85 by ISO lookup). -/
def adposition : Adposition.AdpositionOrder :=
  Adposition.AdpositionOrder.ofWALS "eng"

namespace Adpositions

/-- *to*: *Mary went to Paris*, *Mary gave the book to John*. -/
def to_ : Adposition :=
  { form := .simple "to", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *on*: *the book on the table*. -/
def on : Adposition :=
  { form := .simple "on", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *at*: *Mary is at home*. -/
def at_ : Adposition :=
  { form := .simple "at", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *from*: *Mary came from Paris*. -/
def from_ : Adposition :=
  { form := .simple "from", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *out*, the intransitive particle: *John threw out the trash*. -/
def out : Adposition :=
  { form := .simple "out", relation := .spatial, complement := [], linearization := [.pre] }

/-- *by*: *the book was written by Mary*, *Mary sat by the window*. -/
def by_ : Adposition :=
  { form := .simple "by", relation := .grammatical, complement := [.np], linearization := [.pre] }

/-- *with*: *Mary cut the bread with a knife*, *Mary left with John*. -/
def with_ : Adposition :=
  { form := .simple "with", relation := .grammatical, complement := [.np],
    linearization := [.pre] }

/-- *for*: the benefactive *Martha carved a toy for the baby*, and with a measure phrase *Mary
was sick for three hours*. -/
def for_ : Adposition :=
  { form := .simple "for", relation := .grammatical, complement := [.np, .measure],
    linearization := [.pre] }

/-- *into*: *the witch turned him into a frog*. -/
def into : Adposition :=
  { form := .simple "into", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *out of*: *Martha carved a toy out of the wood*. -/
def outOf : Adposition :=
  { form := .complex ["out", "of"], relation := .spatial, complement := [.np],
    linearization := [.pre] }

/-- *in*: *the trash in the kitchen*, and with a measure phrase *Mary wrote a paper in three
days*, *Mary hasn't been sick in years*. -/
def in_ : Adposition :=
  { form := .simple "in", relation := .spatial, complement := [.np, .measure],
    linearization := [.pre] }

/-- *ago*, the postposition: *Mary left three days ago*. -/
def ago : Adposition :=
  { form := .simple "ago", relation := .temporal, complement := [.measure],
    linearization := [.post] }

end Adpositions

end English
