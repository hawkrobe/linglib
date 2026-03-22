import Linglib.Core.Polarity
import Linglib.Theories.Semantics.Questions.AnsweringSystems
import Linglib.Phenomena.Questions.Basic
import Linglib.Fragments.Swedish.AnswerParticles

/-!
# Polar Answer Structure
@cite{holmberg-2016}

Yes/no answers are question-specific structures, not instances of
general fragment interpretation or ellipsis.

## Holmberg's Analysis

@cite{holmberg-2016} argues that yes/no answers are elliptical full clauses
with the following structure:

    [FocP yes/no Foc⁰ [PolP ... [±Pol] ... ]]

The PolP is elided under identity with the question's PolP. What
remains is the polarity particle in FocP.

This is distinct from general fragment answers (see
`Phenomena/Ellipsis/FragmentAnswers.lean`), which involve wh-question
fragments interpreted via noisy channel or syntactic ellipsis. Yes/no
answers specifically involve:

1. **PolP identity**: the elided PolP must match the question's PolP
2. **Polarity valuation**: the particle values the [±Pol] feature
3. **Focus structure**: the particle sits in Spec-FocP

## Diagnostic: Negative Questions

The key diagnostic is what "yes" means in response to "Doesn't he drink?":

- **Truth-based** (Japanese, Mandarin): "yes" = "he doesn't drink"
  The particle affirms the question's proposition.
- **Polarity-based** (English, Swedish): "yes" = "he does drink"
  The particle assigns [+Pol] to the answer clause.

This variation is captured by `AnsweringSystem` (see
`Theories/Semantics/Questions/AnsweringSystems.lean`).
-/

namespace Phenomena.Questions.PolarAnswerStructure

open Semantics.Questions (AnsweringSystem AnswerStrategy PolarAnswerProfile)

/-- A polar answer datum with answering-system annotation.

    Extends `QAPair` with information about how the answer relates to
    the polarity of the question — critical for cross-linguistic comparison. -/
structure PolarAnswerDatum where
  /-- The polar question -/
  question : String
  /-- The answer particle or verb echo -/
  answer : String
  /-- The proposition expressed by the answer -/
  meaning : String
  /-- Is the question negated? -/
  negativeQuestion : Bool
  /-- The polarity of the answer clause -/
  answerPolarity : Core.Polarity
  /-- Is this answer felicitous? -/
  felicitous : Bool := true
  /-- Language -/
  language : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- English positive question → "yes" = positive (polarity-based). -/
def english_yes : PolarAnswerDatum :=
  { question := "Does John drink?"
  , answer := "Yes"
  , meaning := "John drinks"
  , negativeQuestion := false
  , answerPolarity := .positive
  , language := "English"
  , source := "Holmberg (2016), Ch. 1"
  }

/-- English negative question → "yes" = positive (polarity-based).
    "Doesn't John drink?" → "Yes" = "He does drink." -/
def english_yes_to_neg : PolarAnswerDatum :=
  { question := "Doesn't John drink?"
  , answer := "Yes"
  , meaning := "John drinks"
  , negativeQuestion := true
  , answerPolarity := .positive
  , language := "English"
  , source := "Holmberg (2016), Ch. 4"
  }

/-- Japanese negative question → "hai" = affirms proposition (truth-based).
    "Kare-wa nomanai no?" → "Hai" = "He doesn't drink." -/
def japanese_hai_to_neg : PolarAnswerDatum :=
  { question := "Kare-wa nomanai no?"
  , answer := "Hai"
  , meaning := "He doesn't drink"
  , negativeQuestion := true
  , answerPolarity := .negative
  , language := "Japanese"
  , source := "Holmberg (2016), Ch. 4"
  }

/-- The diagnostic in action: English and Japanese give opposite answers
    to negative questions. -/
theorem answering_systems_diverge :
    english_yes_to_neg.answerPolarity ≠ japanese_hai_to_neg.answerPolarity := by decide

/-- English polar answer profile. -/
def englishProfile : PolarAnswerProfile :=
  { system := .polarityBased
  , strategy := .particle
  , hasPolarityReversal := false
  }

/-- Japanese polar answer profile. -/
def japaneseProfile : PolarAnswerProfile :=
  { system := .truthBased
  , strategy := .particle
  , hasPolarityReversal := false
  }

/-- Swedish polar answer profile (three-way: ja/nej/jo).
    Derived from `Fragments.Swedish.AnswerParticles.profile`. -/
def swedishProfile : PolarAnswerProfile :=
  Fragments.Swedish.AnswerParticles.profile

/-- Finnish polar answer profile (mixed: verb echo + *kyllä*, polarity-based). -/
def finnishProfile : PolarAnswerProfile :=
  { system := .polarityBased
  , strategy := .mixed
  , hasPolarityReversal := false
  }

/-- Mandarin polar answer profile (mixed: V-not-V + *shì/bú shì*, truth-based). -/
def mandarinProfile : PolarAnswerProfile :=
  { system := .truthBased
  , strategy := .mixed
  , hasPolarityReversal := false
  }

end Phenomena.Questions.PolarAnswerStructure
