import Linglib.Discourse.Roles
import Linglib.Data.UD.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Mood Categories
[holmberg-2016] [rizzi-1997] [lakoff-1970]

The definitions core of `Semantics/Mood/`: the category enums for
grammatical mood and illocutionary force, their cross-product
`ClauseType`, the lexical classification of mood-selecting predicates,
and the corpus bridge from `UD.Mood`. This file carries the categories
only; their semantics lives in the sibling `Semantics/Mood/` files
(`Situation`, `Eventuality`, `Dynamic`, `Component`, `Modal`, `State`,
`Verbal`, `SpeechEvent`), and the discourse-act extensions of force
(Searle classes, direction of fit) in `Discourse/SpeechAct.lean`.

## Main declarations

* `Grammatical`, `SubjunctiveType` — verb-morphological mood.
* `Illocutionary`, `Illocutionary.authority` — speech-act force
  (the F in F(p)) and its epistemic-authority assignment.
* `ClauseType` — force × mood. The dimensions are independent
  ([holmberg-2016]): a clause can be [interrogative, indicative]
  ("Does he sleep?") or [interrogative, subjunctive] (Spanish "¿Que
  duerma?"). Both are distinct from `SpeasTenny2003.SAPMood`.
* `Selector` — mood selection by embedding predicate class.
* `UD.Mood.toClauseType` — corpus bridge.
-/

namespace Semantics.Mood

open Discourse (DiscourseRole)

/-! ### Grammatical mood -/

/-- Grammatical (verb-morphological) mood: the indicative/subjunctive contrast. -/
inductive Grammatical where
  /-- The default, "realis" mood. -/
  | indicative
  /-- The non-default, "irrealis" mood. -/
  | subjunctive
  deriving DecidableEq, Repr, Inhabited

/-- The subjunctive functions that individual languages grammaticalize. -/
inductive SubjunctiveType where
  /-- Contrary-to-fact conditionals. -/
  | counterfactual
  /-- Epistemic uncertainty. -/
  | dubitative
  /-- Wishes and desires. -/
  | optative
  /-- Epistemic or circumstantial possibility. -/
  | potential
  /-- [mendes-2025]'s Subordinate Future: present morphology, future reference. -/
  | subordinateFuture
  deriving DecidableEq, Repr

/-! ### Illocutionary force -/

/-- Illocutionary mood: the speech-act force of an utterance — the F in F(p). -/
inductive Illocutionary where
  | declarative
  | interrogative
  | imperative
  | promissive
  | exclamative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The participant with epistemic authority for each force ([lakoff-1970]):
the addressee for interrogatives, the speaker otherwise. -/
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

/-- A clause type: the independent pairing of illocutionary force with
grammatical mood ([holmberg-2016], [rizzi-1997]). -/
structure ClauseType where
  /-- The illocutionary force: the speech act performed. -/
  force : Illocutionary
  /-- The grammatical mood: verb morphology. -/
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

/-- The epistemic authority of a clause type, via its force. -/
def ClauseType.authority (ct : ClauseType) : DiscourseRole :=
  Illocutionary.authority ct.force

/-- Polar questions have addressee authority regardless of mood. -/
theorem polarQuestion_addressee_authority :
    ClauseType.polarQuestion.authority = .addressee := rfl

/-! ### Mood selection by predicate class -/

/-- The mood-selection class of an embedding predicate; the projection onto
the semantic operators is `Selector.toVerbalOp` (`Semantics/Mood/Verbal.lean`). -/
inductive Selector where
  /-- Indicative-selecting: *know*, *see*, *believe*. -/
  | indicativeSelecting
  /-- Robustly subjunctive-selecting: *want*, *wish*, *demand*, *intend*. -/
  | subjunctiveSelecting
  /-- Variable across languages: *hope*, *expect* ([grano-2024], Table 1). -/
  | crossLinguisticallyVariable
  /-- Pragmatically flexible: *say*, *think*. -/
  | moodNeutral
  deriving DecidableEq, Repr

end Semantics.Mood

/-! ### Bridge to UD.Mood

`UD.Mood` is a flat enum conflating illocutionary force (Imp, Jus, Adm)
with grammatical mood (Ind, Sub) and finer irrealis subtypes (Cnd, Opt,
Pot, Nec, Irr). The bridge picks the most defensible default
cross-product:

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
-/

namespace UD.Mood

/-- The default force × mood cross-product for a `UD.Mood` value —
non-injective by design, since `UD.Mood` draws finer irrealis
distinctions than force × mood records. -/
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
