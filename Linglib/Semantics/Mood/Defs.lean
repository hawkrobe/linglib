import Linglib.Discourse.Roles
import Linglib.Data.UD.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Mood Categories
[holmberg-2016] [rizzi-1997] [lakoff-1970]

The definitions core of `Semantics/Mood/`: the category enums for
grammatical mood and illocutionary force, their cross-product
`ClauseType`, the lexical classification of mood-selecting predicates,
and the corpus bridge from `UD.Mood`.

The semantic content of these categories lives downstream:
situation-level operators in `Semantics/Mood/Situation.lean`
([mendes-2025]: SUBJ introduces a situation dref, IND retrieves),
event-level operators in `Semantics/Mood/Eventuality.lean`
([grano-2024]: `Grammatical.eventDenotation` — indicative closes the
event argument, subjunctive leaves it open), the dynamic lifts in
`Semantics/Mood/Dynamic.lean` (`Grammatical.dynOp` — indicative
eliminative, subjunctive generative), and the component/modal layer in
`Semantics/Mood/{Component,Modal,State,Verbal}.lean`. Discourse-act
extensions of force (Searle classes, direction of fit, preparatory
conditions) live in `Discourse/SpeechAct.lean`, which imports this
file; the split keeps the category layer free of pragmatic-act
commitments. `DiscourseRole` lives in `Discourse/Roles.lean` because
it is about discourse participants, not mood.

## Main declarations

* `Grammatical`, `SubjunctiveType` — verb-morphological mood.
* `Illocutionary`, `Illocutionary.authority` — speech-act force
  (the F in F(p)) and its epistemic-authority assignment.
* `ClauseType` — force × mood, the two dimensions orthogonal.
* `Selector` — mood selection by embedding predicate class.
* `UD.Mood.toClauseType` — corpus bridge.

Grammatical mood and illocutionary force are independent dimensions
([holmberg-2016]): a clause can be [interrogative, indicative] ("Does
he sleep?") or [interrogative, subjunctive] (Spanish "¿Que duerma?").
Both are distinct from `SpeasTenny2003.SAPMood` (Speas & Tenny's 2×2
configuration).
-/

namespace Semantics.Mood

open Discourse (DiscourseRole)

/-! ### Grammatical mood -/

/--
Grammatical mood categories.

Following the typological literature:
- **Indicative**: The default, "realis" mood
- **Subjunctive**: Non-default, "irrealis" mood (covers many subtypes)
-/
inductive Grammatical where
  | indicative
  | subjunctive
  deriving DecidableEq, Repr, Inhabited

/--
Subjunctive subtypes (for finer-grained analysis).

Different languages grammaticalize different subjunctive functions:
- Counterfactual: contrary-to-fact conditionals
- Dubitative: epistemic uncertainty
- Optative: wishes and desires
- Potential: epistemic/circumstantial possibility
-/
inductive SubjunctiveType where
  | counterfactual  -- contrary to fact
  | dubitative      -- epistemic uncertainty
  | optative        -- wishes
  | potential        -- possibility
  | subordinateFuture  -- Mendes' SF (present morphology, future reference)
  deriving DecidableEq, Repr

/-! ### Illocutionary force -/

/-- Illocutionary mood — the speech-act force of an utterance.

    Distinct from `Grammatical` (indicative/subjunctive morphology) and the
    Minimalist `SAPMood` (configurational). This classifies the pragmatic
    act performed — the F in F(p). -/
inductive Illocutionary where
  | declarative
  | interrogative
  | imperative
  | promissive
  | exclamative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Which participant holds epistemic authority for a given illocutionary mood.

    [lakoff-1970]: in declaratives, imperatives, and promissives the
    speaker is the seat of knowledge; in interrogatives the addressee is. -/
def Illocutionary.authority : Illocutionary → DiscourseRole
  | .declarative   => .speaker
  | .interrogative  => .addressee
  | .imperative     => .speaker
  | .promissive     => .speaker
  | .exclamative    => .speaker

/-! ### Clause type: force × mood

| Force         | Mood        | Example                              |
|---------------|-------------|--------------------------------------|
| declarative   | indicative  | "John sleeps."                       |
| declarative   | subjunctive | "Long live the king!"                |
| interrogative | indicative  | "Does John sleep?"                   |
| interrogative | subjunctive | "¿Que duerma?" (Sp. deliberative)    |
| imperative    | —           | "Sleep!" (mood often neutralized)    |
-/

/-- A clause's type: the independent pairing of illocutionary force
    with grammatical mood ([holmberg-2016], [rizzi-1997]). -/
structure ClauseType where
  /-- Illocutionary force: the speech act performed -/
  force : Illocutionary
  /-- Grammatical mood: verb morphology -/
  mood : Grammatical
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
  Illocutionary.authority ct.force

/-- Polar questions have addressee authority regardless of mood. -/
theorem polarQuestion_addressee_authority :
    ClauseType.polarQuestion.authority = .addressee := rfl

/-! ### Mood selection by predicate class -/

/--
Mood selection by embedding predicates.

Certain predicates select for specific moods in their complement:
- "know", "see" → typically indicative
- "want", "wish" → robustly subjunctive cross-linguistically
- "hope" → cross-linguistically variable ([grano-2024], Table 1)
- "say", "think" → mood-neutral (pragmatically flexible)

The projection onto the semantic operators is
`Selector.toVerbalOp` (`Semantics/Mood/Verbal.lean`).
-/
inductive Selector where
  | indicativeSelecting          -- "know", "see", "believe"
  | subjunctiveSelecting         -- "want", "wish", "demand", "intend"
  | crossLinguisticallyVariable  -- "hope", "expect": SBJV in some languages,
                                 -- IND in others ([grano-2024], Table 1)
  | moodNeutral                  -- "say", "think" (pragmatically flexible)
  deriving DecidableEq, Repr

end Semantics.Mood

/-! ### Bridge to UD.Mood -/

namespace UD.Mood

/-- Project a `UD.Mood` feature value to a `Semantics.Mood.ClauseType`.

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
def toClauseType : UD.Mood → Semantics.Mood.ClauseType
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
