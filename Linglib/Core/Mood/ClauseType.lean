import Linglib.Core.Mood.Basic
import Linglib.Core.Mood.IllocutionaryMood
import Linglib.Core.Discourse.Roles
import Linglib.Core.Lexical.UD

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

`ClauseType` lives in `Core/Mood/` because the file is intrinsically about
the mood-category cross-product. The discourse-act extensions of force
(Searle classes, direction of fit, preparatory conditions) live in
`Core/Discourse/IllocutionaryForce.lean`.
-/

namespace Core.Mood

open Core.Discourse (DiscourseRole)

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

-- ════════════════════════════════════════════════════════════════
-- § Bridge to UD.Mood
-- ════════════════════════════════════════════════════════════════

end Core.Mood

-- ════════════════════════════════════════════════════════════════
-- § Bridge to UD.Mood
-- ════════════════════════════════════════════════════════════════

namespace UD.Mood

/-- Project a `UD.Mood` feature value to a `Core.Mood.ClauseType`.

    `UD.Mood` is a flat enum that conflates illocutionary force
    (Imp, Jus, Adm) with grammatical mood (Ind, Sub) with finer
    irrealis subtypes (Cnd, Opt, Pot, Nec, Irr). The bridge picks the
    most defensible default cross-product:

    | UD.Mood | force         | mood        |
    |---------|---------------|-------------|
    | Ind     | declarative   | indicative  |
    | Sub     | declarative   | subjunctive |
    | Imp     | imperative    | indicative  |
    | Cnd     | declarative   | subjunctive |
    | Opt     | declarative   | subjunctive |
    | Jus     | imperative    | subjunctive |
    | Pot     | declarative   | subjunctive |
    | Qot     | declarative   | indicative  |
    | Adm     | exclamative   | indicative  |
    | Nec     | declarative   | subjunctive |
    | Irr     | declarative   | subjunctive |

    The mapping is non-injective by design — UD.Mood draws finer
    distinctions on the irrealis side than (force × mood) records. -/
def toClauseType : UD.Mood → Core.Mood.ClauseType
  | .Ind => { force := .declarative, mood := .indicative }
  | .Sub => { force := .declarative, mood := .subjunctive }
  | .Imp => { force := .imperative,  mood := .indicative }
  | .Cnd => { force := .declarative, mood := .subjunctive }
  | .Opt => { force := .declarative, mood := .subjunctive }
  | .Jus => { force := .imperative,  mood := .subjunctive }
  | .Pot => { force := .declarative, mood := .subjunctive }
  | .Qot => { force := .declarative, mood := .indicative }
  | .Adm => { force := .exclamative, mood := .indicative }
  | .Nec => { force := .declarative, mood := .subjunctive }
  | .Irr => { force := .declarative, mood := .subjunctive }

/-- The UD `Imp` mood projects to imperative force. -/
theorem Imp_is_imperative :
    (toClauseType .Imp).force = .imperative := rfl

/-- The UD `Sub` mood projects to subjunctive grammatical mood. -/
theorem Sub_is_subjunctive :
    (toClauseType .Sub).mood = .subjunctive := rfl

end UD.Mood
