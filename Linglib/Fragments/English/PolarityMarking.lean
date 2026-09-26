module

public import Linglib.Semantics.Polarity.Marking

/-!
# English polarity marking

English marks a switch from negative to positive polarity, the contradiction of a negative
claim, with emphatic *do*: the auxiliary bears a pitch accent in an affirmative sentence that
contradicts a prior negative one, *He doesn't like cats. He DOES like cats*. Wilder separates
this Verum-focus use, focus on the truth of the proposition, from the contrastive-topic use in
which *do* marks a topic shift, *He DOES like cats, but he doesn't like dogs*; only the first
is a polarity-marking device, sentence-internal, available in contrast and in correction, and
the English analogue of German Verum focus.

## Main definitions

* `English.PolarityMarking.emphaticDo`: the Verum-focus use of emphatic *do*.

## References

* [wilder-2013]
-/

@[expose] public section

namespace English.PolarityMarking

open PolarityMarker (Strategy Env)

/-- Emphatic *do* in its Verum-focus use, a pitch accent on the auxiliary of an affirmative
sentence contradicting a negative one, available sentence-internally in contrast and in
correction. -/
def emphaticDo : PolarityMarker where
  label := "emphatic do"
  prosodicTarget := some "auxiliary do"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .verumFocus

/-- The polarity-marking devices. -/
def markers : List PolarityMarker := [emphaticDo]

end English.PolarityMarking
