import Linglib.Discourse.Roles
import Linglib.Data.UD.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Mood Categories

A clause carries two independent mood dimensions: an illocutionary
force (the speech-act type — the F in F(p)) and a grammatical mood
(the indicative/subjunctive verb morphology). The dimensions cross
freely ([holmberg-2016]): a polar question is [interrogative,
indicative], while the Spanish deliberative "¿Que duerma?" is
[interrogative, subjunctive]. This file defines the two category
enums, their pairing `ClauseType`, the mood-selection classes of
embedding predicates, and the bridge from the UD `Mood` feature.

## Main declarations

* `Grammatical`, `SubjunctiveType` — verb-morphological mood.
* `Illocutionary`, `Illocutionary.authority` — speech-act force and
  its epistemic-authority assignment.
* `ClauseType` — force × mood.
* `Selector` — mood selection by embedding predicate class.
* `Component`, `HasTarget` — [portner-2018]'s classification: the
  coordinate of the mood state each category operates on.
* `UD.Mood.toClauseType` — corpus bridge.

The Searle-class and direction-of-fit API for `Illocutionary` is in
`Discourse/SpeechAct.lean`.
-/

namespace Mood

open Discourse (DiscourseRole)

/-! ### Grammatical mood -/

/-- Grammatical (verb-morphological) mood. -/
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

/-- The epistemic authority of a clause type, via its force. -/
def ClauseType.authority (ct : ClauseType) : DiscourseRole :=
  Illocutionary.authority ct.force

/-! ### Mood components -/

/-- The component of the mood state that a mood-bearing object operates
on ([portner-2018], Ch. 4). -/
inductive Component where
  /-- The information coordinate (`State.info`). -/
  | informational
  /-- The ordering coordinate (`State.order`). -/
  | preferential
  /-- The inquiry coordinate (`State.inquiry`). -/
  | inquisitive
  deriving DecidableEq, Repr

/-- The class of mood-bearing types: `target m` is the component the
context selecting `m` quantifies over, not an operation `m` performs. -/
class HasTarget (M : Type*) where
  target : M → Component

/-- Sentence-mood targets ([portner-2018], Ch. 3). Promissive and
exclamative are linglib extensions; the exclamative assignment
conflicts with its null direction of fit (`Discourse/SpeechAct.lean`)
and is a conjectural placeholder. -/
instance : HasTarget Illocutionary where
  target
    | .declarative   => .informational
    | .imperative    => .preferential
    | .promissive    => .preferential
    | .interrogative => .inquisitive
    | .exclamative   => .informational

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

end Mood

/-! ### Bridge to UD.Mood -/

namespace UD.Mood

/-- The default `ClauseType` for a `UD.Mood` value. The UD feature is a
flat enum conflating force with mood, so the map is a non-injective
default cross-product. -/
def toClauseType : UD.Mood → Mood.ClauseType
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

end UD.Mood
