module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# English adpositions

The closed-class adpositions of English as `Adposition` entries: the spatial *to*, *on*, *in*,
*into*, *at*, *from*, *out of* and the particle *out*, the grammatical *by*, *with* and *for*,
and the adpositions that take a measure phrase, *for three hours*, *in three hours* and the
postposition *three days ago*. Which interval
a measure applies to, the runtime of an atelic or telic eventuality ([dowty-1979]'s *for* and *in*
tests, `Aspect.forXPrediction` and `Aspect.inXPrediction`), the offset from the utterance time, or
under negation and the perfect the gap since the last event, is not lexical and is left to the
studies; the polarity item *in years* is `English.PolarityItems.inYears`, the temporal
connectives *before*, *after*, *since*, *until* and *by* are `English.TemporalConnectives`, and the
agent-marking of passive *by* is a study-level refinement.

## References

* [dowty-1979]
-/

@[expose] public section

namespace English

namespace Adpositions

/-- *to*, as in *Mary went to Paris*, *Mary gave the book to John*. -/
def to_ : Adposition :=
  { form := .simple "to", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *on*, as in *the book on the table*. -/
def on : Adposition :=
  { form := .simple "on", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *at*, as in *Mary is at home*. -/
def at_ : Adposition :=
  { form := .simple "at", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *from*, as in *Mary came from Paris*. -/
def from_ : Adposition :=
  { form := .simple "from", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *out*, the intransitive particle, as in *John threw out the trash*. -/
def out : Adposition :=
  { form := .simple "out", relation := .spatial, complement := [], linearization := [.pre] }

/-- *by*, as in *the book was written by Mary*, *Mary sat by the window*. -/
def by_ : Adposition :=
  { form := .simple "by", relation := .grammatical, complement := [.np], linearization := [.pre] }

/-- *with*, as in *Mary cut the bread with a knife*, *Mary left with John*. -/
def with_ : Adposition :=
  { form := .simple "with", relation := .grammatical, complement := [.np],
    linearization := [.pre] }

/-- *for*, as in the benefactive *Martha carved a toy for the baby*, and with a measure phrase *Mary
was sick for three hours*. -/
def for_ : Adposition :=
  { form := .simple "for", relation := .grammatical, complement := [.np, .measure],
    linearization := [.pre] }

/-- *into*, as in *the witch turned him into a frog*. -/
def into : Adposition :=
  { form := .simple "into", relation := .spatial, complement := [.np], linearization := [.pre] }

/-- *out of*, as in *Martha carved a toy out of the wood*. -/
def outOf : Adposition :=
  { form := .complex ["out", "of"], relation := .spatial, complement := [.np],
    linearization := [.pre] }

/-- *in*, as in *the trash in the kitchen*, and with a measure phrase *Mary wrote a paper in three
days*, *Mary hasn't been sick in years*. -/
def in_ : Adposition :=
  { form := .simple "in", relation := .spatial, complement := [.np, .measure],
    linearization := [.pre] }

/-- *ago*, the postposition, as in *Mary left three days ago*. -/
def ago : Adposition :=
  { form := .simple "ago", relation := .temporal, complement := [.measure],
    linearization := [.post] }

end Adpositions

end English
