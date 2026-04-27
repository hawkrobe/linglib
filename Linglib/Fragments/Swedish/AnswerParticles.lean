import Linglib.Features.Polarity
import Linglib.Features.InformationStructure
import Linglib.Features.AnsweringSystem

/-!
# Swedish Answer Particles
@cite{holmberg-2016}

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

namespace Fragments.Swedish.AnswerParticles

open Features.Polarity
open Features.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy PolarityMarkingEnv)
open Features (AnsweringSystem AnswerStrategy PolarAnswerProfile)

/-- A Swedish answer particle entry. -/
structure AnswerParticle where
  /-- Citation form -/
  form : String
  /-- The polarity this particle assigns -/
  polarity : Features.Polarity
  /-- Does this particle require a negative context? -/
  requiresNegativeContext : Bool
  /-- Is this a polarity-reversing particle? -/
  isPolarityReversal : Bool := requiresNegativeContext
  /-- Is this particle blocked (ungrammatical) in negative contexts?
      @cite{holmberg-2016} p165: Swedish *ja* is ungrammatical (not just
      infelicitous) as a response to negative questions. -/
  blockedInNegativeContext : Bool := false
  deriving Repr

/-- *ja* — standard affirmative. Assigns [+Pol].
    Blocked in negative contexts: "Dricker han inte?" → *"Ja" is
    ungrammatical (@cite{holmberg-2016}, p165). Swedish uses *jo* instead. -/
def ja : AnswerParticle :=
  { form := "ja"
  , polarity := .positive
  , requiresNegativeContext := false
  , blockedInNegativeContext := true
  }

/-- *nej* — standard negative. Assigns [-Pol]. -/
def nej : AnswerParticle :=
  { form := "nej"
  , polarity := .negative
  , requiresNegativeContext := false
  }

/-- *jo* — polarity-reversing affirmative. Assigns [+Pol] while
    contradicting a negative context.

    "Dricker han inte?" (Doesn't he drink?)
    → "Jo" = "He does drink" (reverses the expected negative polarity)

    Cannot be used in response to positive questions or out of the blue:
    "Dricker han?" (Does he drink?)
    → *"Jo" is infelicitous (no negative context to reverse) -/
def jo : AnswerParticle :=
  { form := "jo"
  , polarity := .positive
  , requiresNegativeContext := true
  }

/-- *jo* is a polarity-reversing particle. -/
theorem jo_is_reversal : jo.isPolarityReversal = true := rfl

/-- *ja* is not polarity-reversing. -/
theorem ja_not_reversal : ja.isPolarityReversal = false := rfl

/-- *jo* and *ja* both assign positive polarity. The difference is
    context: *jo* requires a negative context, *ja* does not. -/
theorem jo_ja_same_polarity : jo.polarity = ja.polarity := rfl

/-- *ja* is blocked in negative contexts — this is why *jo* exists. -/
theorem ja_blocked_in_negative : ja.blockedInNegativeContext = true := rfl

/-- *ja* and *jo* are in complementary distribution: *ja* is blocked where
    *jo* is required (negative contexts), and *jo* is blocked where *ja*
    is available (positive contexts). -/
theorem ja_jo_complementary :
    ja.blockedInNegativeContext = true ∧ jo.requiresNegativeContext = true ∧
    ja.requiresNegativeContext = false ∧ jo.blockedInNegativeContext = false := ⟨rfl, rfl, rfl, rfl⟩

/-- *jo* — Swedish polarity-reversing affirmative particle.
    Assigns [+Pol] while contradicting a negative context.
    Clause-initial or standalone response; not sentence-internal.
    Correction-only: requires a negative context to reverse.
    @cite{holmberg-2016}: paradigm example of polarity-reversing particle,
    same class as German *doch* and French *si*. -/
abbrev joMarking : PolarityMarkingEntry where
  label := "jo"
  form := some "jo"
  environments := {.correction}
  strategy := .polarityReversal

-- Per-entry verification theorems
theorem joMarking_form : joMarking.form = some "jo" := rfl
theorem joMarking_not_sentenceInternal : PolarityMarkingEnv.sentenceInternal ∉ joMarking.environments := by decide
theorem joMarking_not_contrastOk : PolarityMarkingEnv.contrast ∉ joMarking.environments := by decide
theorem joMarking_correctionOk : PolarityMarkingEnv.correction ∈ joMarking.environments := by decide
theorem joMarking_strategy : joMarking.strategy = .polarityReversal := rfl

def allPolarityMarkings : List PolarityMarkingEntry := [joMarking]

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

end Fragments.Swedish.AnswerParticles
