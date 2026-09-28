module

public import Linglib.Semantics.Polarity.Marking

/-!
# German polarity marking

German marks a switch from negative to positive polarity with Verum focus, a high-falling pitch
accent on the finite verb, [hohle-1992], and not with a sentence-internal affirmative particle:
in the production study of [turco-braun-dimroth-2014] speakers never produced *schon* or
*wohl* in that function, and used *doch* only as a separate utterance preceding a Verum focus
utterance in corrections. The polarity particles *ja*, *nein* and *doch* and the
clause-internal modal particle *doch* live in `German/Particles`,
and VERUM in questions in `Question.VerumFocus`.

## References

* [turco-braun-dimroth-2014]
* [hohle-1992]
* [holmberg-2016]
-/

@[expose] public section

namespace German.PolarityMarking

open PolarityMarker

/-- Verum focus, a pitch accent on the finite verb: sentence-internal, available in contrast and
in correction, the dominant German strategy in both. -/
abbrev verumFocus : PolarityMarker where
  label := "Verum focus"
  prosodicTarget := some "finite verb"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .verumFocus

/-- *doch* as a separate utterance preceding a Verum focus utterance: a polarity-reversing
particle, [holmberg-2016], available in corrections only and not sentence-internal. -/
abbrev dochPreUtterance : PolarityMarker where
  label := "doch (pre-utterance)"
  form := some "doch"
  environments := {.correction}
  strategy := .polarityReversal

end German.PolarityMarking
