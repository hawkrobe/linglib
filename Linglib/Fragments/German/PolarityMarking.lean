import Linglib.Semantics.Polarity.Marking
import Linglib.Features.AnsweringSystem

/-!
# German Polarity-Marking Strategies
[turco-braun-dimroth-2014] [hohle-1992] [romero-han-2004]

Lexical entries for how German marks polarity switches (negation → affirmation).

The key finding of [turco-braun-dimroth-2014] is that German does NOT use
sentence-internal particles for polarity switches. Instead, German relies on
Verum focus: a pitch accent on the finite verb. The particle
*doch* can appear pre-utterance in corrections but is not sentence-internal
in the relevant sense.

This file is named "PolarityMarking" rather than "Particles" precisely because
German's strategy is non-particulate.

## Cross-Module Connections

- `Semantics.Questions.VerumFocus`: VERUM in questions — a
  different phenomenon from the declarative Verum focus encoded here
- `German.Particles`: German *denn* (question-flavoring)

-/

namespace German.PolarityMarking

open Semantics.Polarity.Marking (Entry Strategy Env)

/-- Verum focus — pitch accent on the finite verb.
    Dominant strategy in German for neg→affirm switches in both contexts.
    Sentence-internal; available in both contrast and correction.
    [hohle-1992], [turco-braun-dimroth-2014]: ~82% in contrast,
    ~78% in correction. -/
abbrev verumFocus : Entry where
  label := "Verum focus"
  prosodicTarget := some "finite verb"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .verumFocus

/-- *doch* — polarity-reversing correction particle ([holmberg-2016]).
    Assigns [+Pol] while contradicting a negative context. Available only
    in corrections, NOT sentence-internal in the sense of
    [turco-braun-dimroth-2014]: it precedes the utterance rather than
    appearing within the VP/middle field. Cross-linguistically the same
    class as Swedish *jo* and French *si*. -/
abbrev dochPreUtterance : Entry where
  label := "doch (pre-utterance)"
  form := some "doch"
  environments := {.correction}
  strategy := .polarityReversal

def allPolarityMarkings : List Entry := [verumFocus, dochPreUtterance]

-- Per-entry verification theorems: verumFocus
theorem vf_prosodicTarget : verumFocus.prosodicTarget = some "finite verb" := rfl
theorem vf_sentenceInternal : Env.sentenceInternal ∈ verumFocus.environments := by decide
theorem vf_contrastOk : Env.contrast ∈ verumFocus.environments := by decide
theorem vf_correctionOk : Env.correction ∈ verumFocus.environments := by decide
theorem vf_strategy : verumFocus.strategy = .verumFocus := rfl

-- Per-entry verification theorems: dochPreUtterance
theorem doch_form : dochPreUtterance.form = some "doch" := rfl
theorem doch_not_sentenceInternal : Env.sentenceInternal ∉ dochPreUtterance.environments := by decide
theorem doch_not_contrastOk : Env.contrast ∉ dochPreUtterance.environments := by decide
theorem doch_correctionOk : Env.correction ∈ dochPreUtterance.environments := by decide
theorem doch_strategy : dochPreUtterance.strategy = .polarityReversal := rfl

/-! ### German answer particles ([holmberg-2016])

The response system in `Features.AnswerParticle` vocabulary. *doch*
here is the answer-particle face of `dochPreUtterance` (the same item
in the [turco-braun-dimroth-2014] marking vocabulary above); its
clause-internal modal-particle homonym lives in `German/Particles.lean`. -/

/-- *ja* — standard affirmative answer particle; positive contexts only
    (like Swedish *ja*). Distinct from the modal particle *ja*
    (`German/Particles.lean`). -/
def jaAnswer : Features.AnswerParticle :=
  { form := "ja", assigns := .positive, respondsTo := [.positive] }

/-- *nein* — standard negative answer particle. -/
def nein : Features.AnswerParticle :=
  { form := "nein", assigns := .negative, respondsTo := [.positive, .negative] }

/-- *doch* — polarity-reversing answer particle: "Kommt er nicht?" →
    "Doch" = "he is coming". -/
def dochAnswer : Features.AnswerParticle :=
  { form := "doch", assigns := .positive, respondsTo := [.negative] }

/-- *doch* is a polarity-reversing particle — derived from its
    assign/respond profile. -/
theorem dochAnswer_is_reversal : dochAnswer.IsReversal := by decide

end German.PolarityMarking
