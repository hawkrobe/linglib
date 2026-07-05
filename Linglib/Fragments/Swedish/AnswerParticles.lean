import Linglib.Features.Polarity
import Linglib.Semantics.Polarity.Marking
import Linglib.Features.AnsweringSystem

/-!
# Swedish Answer Particles
[holmberg-2016]

Answer particles are pro-sentential — they stand alone as utterances
rather than associating with a host constituent — so they deliberately
do not instantiate the host-associated `Syntax/Particle` core.

Swedish has a three-way answer particle system:
- *ja* — affirmative ("yes")
- *nej* — negative ("no")
- *jo* — polarity-reversing affirmative (contradicts a negative context)

*Jo* is the paradigm example of a polarity-reversing particle, the same
class as German *doch* and French *si*. It assigns [+Pol] while
presupposing a negative context (negative question or negative assertion).

Swedish is polarity-based: "Dricker han inte?" → "Ja" = "He does drink."

Swedish also allows verb-echo answers alongside particles (mixed strategy).
-/

namespace Swedish.AnswerParticles

open Features.Polarity
open Semantics.Polarity.Marking (Entry Strategy Env)
open Features (AnsweringSystem AnswerStrategy PolarAnswerProfile)

/-- *ja* — standard affirmative. Assigns [+Pol]. Responds only to
    positive contexts: "Dricker han inte?" → *"Ja" is ungrammatical
    ([holmberg-2016], p165). Swedish uses *jo* instead. -/
def ja : Features.AnswerParticle :=
  { form := "ja", assigns := .positive, respondsTo := [.positive] }

/-- *nej* — standard negative. Assigns [-Pol]; responds to positive and
    negative contexts alike. -/
def nej : Features.AnswerParticle :=
  { form := "nej", assigns := .negative, respondsTo := [.positive, .negative] }

/-- *jo* — polarity-reversing affirmative: "Dricker han inte?" → "Jo" =
    "He does drink". Infelicitous responding to positive questions or
    out of the blue (no negative context to reverse). -/
def jo : Features.AnswerParticle :=
  { form := "jo", assigns := .positive, respondsTo := [.negative] }

/-- *jo* is a polarity-reversing particle — derived from its
    assign/respond profile. -/
theorem jo_is_reversal : jo.IsReversal := by decide

/-- *ja* is not polarity-reversing. -/
theorem ja_not_reversal : ¬ ja.IsReversal := by decide

/-- *jo* and *ja* both assign positive polarity; only the antecedent
    contexts differ. -/
theorem jo_ja_same_polarity : jo.assigns = ja.assigns := rfl

/-- *ja* and *jo* partition the context polarities: *ja* is blocked
    where *jo* is required (negative contexts) and vice versa. -/
theorem ja_jo_complementary :
    Features.Polarity.negative ∉ ja.respondsTo ∧
    Features.Polarity.positive ∉ jo.respondsTo := by decide

/-- *jo* — Swedish polarity-reversing affirmative particle.
    Assigns [+Pol] while contradicting a negative context.
    Clause-initial or standalone response; not sentence-internal.
    Correction-only: requires a negative context to reverse.
    [holmberg-2016]: paradigm example of polarity-reversing particle,
    same class as German *doch* and French *si*. -/
abbrev joMarking : Entry where
  label := "jo"
  form := some "jo"
  environments := {.correction}
  strategy := .polarityReversal

-- Per-entry verification theorems
theorem joMarking_form : joMarking.form = some "jo" := rfl
theorem joMarking_not_sentenceInternal : Env.sentenceInternal ∉ joMarking.environments := by decide
theorem joMarking_not_contrastOk : Env.contrast ∉ joMarking.environments := by decide
theorem joMarking_correctionOk : Env.correction ∈ joMarking.environments := by decide
theorem joMarking_strategy : joMarking.strategy = .polarityReversal := rfl

def allPolarityMarkings : List Entry := [joMarking]

/-- Swedish polar answer profile: polarity-based, mixed strategy
    (particles + verb echo), with polarity reversal (*jo*). -/
def profile : PolarAnswerProfile :=
  { system := .polarityBased
  , strategy := .mixed
  , hasPolarityReversal := true
  }

/-- Swedish is polarity-based. -/
theorem swedish_polarity_based : profile.system = .polarityBased := rfl

/-- Swedish has polarity reversal. -/
theorem swedish_has_reversal : profile.hasPolarityReversal = true := rfl

end Swedish.AnswerParticles
