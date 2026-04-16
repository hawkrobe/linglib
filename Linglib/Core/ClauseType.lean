import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Core.GrammaticalMood

/-!
# Clause Type: Force × Mood
@cite{holmberg-2016} @cite{rizzi-1997}

A clause type is a pair of independent dimensions:
- **Force** (`IllocutionaryMood`): declarative, interrogative, imperative, ...
- **Mood** (`GramMood`): indicative, subjunctive

These are orthogonal — @cite{holmberg-2016}'s analysis requires both:
a polar question is [interrogative, indicative], while a deliberative
subjunctive question is [interrogative, subjunctive].

| Force         | Mood        | Example                              |
|---------------|-------------|--------------------------------------|
| declarative   | indicative  | "John sleeps."                       |
| declarative   | subjunctive | "Long live the king!"                |
| interrogative | indicative  | "Does John sleep?"                   |
| interrogative | subjunctive | "¿Que duerma?" (Sp. deliberative)    |
| imperative    | —           | "Sleep!" (mood often neutralized)    |
-/

namespace Core

open Core.Discourse (IllocutionaryMood DiscourseRole moodAuthority)

/-- A clause's type: the independent pairing of illocutionary force
    with grammatical mood. -/
structure ClauseType where
  /-- Illocutionary force: the speech act performed -/
  force : IllocutionaryMood
  /-- Grammatical mood: verb morphology -/
  mood : GramMood
  deriving DecidableEq, Repr

/-- A standard declarative-indicative clause. -/
def ClauseType.declInd : ClauseType :=
  { force := .declarative, mood := .indicative }

/-- A standard polar question (interrogative-indicative). -/
def ClauseType.polarQuestion : ClauseType :=
  { force := .interrogative, mood := .indicative }

/-- Force and mood are independent: changing one doesn't change the other. -/
theorem force_mood_independent :
    ClauseType.declInd.mood = ClauseType.polarQuestion.mood ∧
    ClauseType.declInd.force ≠ ClauseType.polarQuestion.force := ⟨rfl, nofun⟩

/-- Map from `ClauseType` to epistemic authority (via force, ignoring mood). -/
def ClauseType.authority (ct : ClauseType) : DiscourseRole :=
  moodAuthority ct.force

/-- Polar questions have addressee authority regardless of mood. -/
theorem polarQuestion_addressee_authority :
    ClauseType.polarQuestion.authority = .addressee := rfl

end Core
