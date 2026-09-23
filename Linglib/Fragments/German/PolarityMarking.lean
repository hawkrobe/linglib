module

public import Linglib.Semantics.Polarity.Marking
public import Linglib.Semantics.Questions.Answering

/-!
# German polarity marking

German marks a switch from negative to positive polarity with Verum focus, a high-falling pitch
accent on the finite verb, [hohle-1992], and not with a sentence-internal affirmative particle:
in the production study of [turco-braun-dimroth-2014] speakers never produced *schon* or
*wohl* in that function, and used *doch* only as a separate utterance preceding a Verum focus
utterance in corrections. The answer particles *ja*, *nein* and the polarity-reversing *doch*
follow [holmberg-2016]. The clause-internal modal particle *doch* lives in `German/Particles`,
and VERUM in questions in `Question.VerumFocus`.

## References

* [turco-braun-dimroth-2014]
* [hohle-1992]
* [holmberg-2016]
-/

@[expose] public section

namespace German.PolarityMarking

open Polarity.Marking

/-- Verum focus, a pitch accent on the finite verb: sentence-internal, available in contrast and
in correction, the dominant German strategy in both. -/
abbrev verumFocus : Entry where
  label := "Verum focus"
  prosodicTarget := some "finite verb"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .verumFocus

/-- *doch* as a separate utterance preceding a Verum focus utterance: a polarity-reversing
particle, [holmberg-2016], available in corrections only and not sentence-internal. -/
abbrev dochPreUtterance : Entry where
  label := "doch (pre-utterance)"
  form := some "doch"
  environments := {.correction}
  strategy := .polarityReversal

/-! ### Answer particles -/

/-- *ja*, the affirmative answer particle, answering positive questions only. -/
def jaAnswer : Question.AnswerParticle :=
  { form := "ja", assigns := .positive, respondsTo := [.positive] }

/-- *nein*, the negative answer particle. -/
def nein : Question.AnswerParticle :=
  { form := "nein", assigns := .negative, respondsTo := [.positive, .negative] }

/-- *doch*, the polarity-reversing answer particle: *Kommt er nicht?* -- *Doch*, he is coming. -/
def dochAnswer : Question.AnswerParticle :=
  { form := "doch", assigns := .positive, respondsTo := [.negative] }

/-- *doch* is a reversal particle by its profile. -/
theorem dochAnswer_is_reversal : dochAnswer.IsReversal := by decide

end German.PolarityMarking
