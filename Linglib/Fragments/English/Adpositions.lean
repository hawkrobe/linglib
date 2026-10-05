module

public import Linglib.Syntax.Category.Adposition.Basic

/-!
# English adpositions

The closed-class adpositions of English as `Adposition` entries: the spatial *to*, *on*, *in*,
*into*, *at*, *from* and *out of*, the particle *out*, and *by*, *with* and *for*, which also
introduce participants. Each entry records the comparative case values it marks, read off the
glosses `Case` gives them, so *to* marks the allative of *went to Paris* and the dative of *gave
the book to John*.

## Implementation notes

* *for*, *in* and the postposition *ago* also take a measure phrase. Which interval a measure
  applies to (Dowty's *for* and *in* tests, `Aspect.forXPrediction` and
  `Aspect.inXPrediction`), the offset from the utterance time, or the gap since the last event
  under negation and the perfect, is not lexical and is left to the studies.
* The polarity item *in years* is `English.PolarityItems.inYears`, and the temporal
  connectives *before*, *after*, *since*, *until* and *by* are `English.TemporalConnectives`.
* The passive agent that *by* marks has no comparative case value; agent marking is left to
  the studies.

## References

* [dowty-1979]
-/

@[expose] public section

namespace English

namespace Adpositions

/-- *to*, as in *Mary went to Paris*, *Mary gave the book to John*. -/
def to_ : Adposition :=
  { morphs := [.free "to"], linearization := {.pre}, functions := {.all, .dat},
    complements := {some .np} }

/-- *on*, as in *the book on the table*. -/
def on : Adposition :=
  { morphs := [.free "on"], linearization := {.pre}, functions := {.sup},
    complements := {some .np} }

/-- *at*, as in *Mary is at home*. -/
def at_ : Adposition :=
  { morphs := [.free "at"], linearization := {.pre}, functions := {.ade},
    complements := {some .np} }

/-- *from*, as in *Mary came from Paris*. -/
def from_ : Adposition :=
  { morphs := [.free "from"], linearization := {.pre}, functions := {.abl},
    complements := {some .np} }

/-- *out*, the particle, as in *John threw out the trash*. -/
def out : Adposition :=
  { morphs := [.free "out"], linearization := ∅, functions := {.ela}, complements := {none} }

/-- *by*, as in *the book was written by Mary*, *Mary sat by the window*. -/
def by_ : Adposition :=
  { morphs := [.free "by"], linearization := {.pre}, functions := {.ade},
    complements := {some .np} }

/-- *with*, as in *Mary cut the bread with a knife*, *Mary left with John*. -/
def with_ : Adposition :=
  { morphs := [.free "with"], linearization := {.pre}, functions := {.inst, .com},
    complements := {some .np} }

/-- *for*, as in the benefactive *Martha carved a toy for the baby*, and with a measure phrase *Mary
was sick for three hours*. -/
def for_ : Adposition :=
  { morphs := [.free "for"], linearization := {.pre}, functions := {.ben},
    complements := {some .np, some .measure} }

/-- *into*, as in *the witch turned him into a frog*. -/
def into : Adposition :=
  { morphs := [.free "into"], linearization := {.pre}, functions := {.ill},
    complements := {some .np} }

/-- *out of*, as in *Martha carved a toy out of the wood*. -/
def outOf : Adposition :=
  { morphs := [.free "out", .free "of"], linearization := {.pre}, functions := {.ela},
    complements := {some .np} }

/-- *in*, as in *the trash in the kitchen*, and with a measure phrase *Mary wrote a paper in three
days*, *Mary hasn't been sick in years*. -/
def in_ : Adposition :=
  { morphs := [.free "in"], linearization := {.pre}, functions := {.ine},
    complements := {some .np, some .measure} }

/-- *ago*, the postposition, as in *Mary left three days ago*. -/
def ago : Adposition :=
  { morphs := [.free "ago"], linearization := {.post}, functions := {.tem},
    complements := {some .measure} }

end Adpositions

end English
