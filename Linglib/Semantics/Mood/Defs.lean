/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.Role
public import Linglib.Syntax.Clause.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Mood categories

This file defines grammatical mood and illocutionary force. Grammatical mood is the
indicative or subjunctive morphology of the verb. Illocutionary force is the speech act an
utterance performs, the F in F(p); each sentence type conventionally performs one force,
`Clause.SentenceType.force`, and a form used for another act, a rising declarative that asks or
an interrogative that requests, is a mismatch between that pairing and the act. The two
dimensions cross freely, as Holmberg observes: a polar question is interrogative and
indicative, while the Spanish deliberative *¿Que duerma?* is interrogative and subjunctive.
Portner classifies each force by the coordinate of the mood state it operates on.

## Main declarations

* `Grammatical`, `SubjunctiveType`: verb-morphological mood.
* `Illocutionary`, `Illocutionary.authority`: speech-act force and Lakoff's epistemic
  authority.
* `Clause.SentenceType.force`: the force a sentence type conventionally performs.
* `Component`, `HasTarget`: Portner's classification by the coordinate of the mood state.

## References

* [holmberg-2016]
* [portner-2018]
* [lakoff-1970]
* [rizzi-1997]
-/

@[expose] public section


namespace Mood


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

/-- The illocutionary force of an utterance is the act it performs, the F in F(p), which its
sentence type conventionally fixes and which form and use may pull apart. -/
inductive Illocutionary where
  | declarative
  | interrogative
  | imperative
  | promissive
  | exclamative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The participant with epistemic authority for each force ([lakoff-1970]):
the addressee for interrogatives, the speaker otherwise. -/
def Illocutionary.authority : Illocutionary → Discourse.Role
  | .declarative   => .speaker
  | .interrogative  => .addressee
  | .imperative     => .speaker
  | .promissive     => .speaker
  | .exclamative    => .speaker

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

end Mood

/-! ### The conventional force of a sentence type -/

/-- The force a sentence type conventionally performs, asking for the three interrogatives and
the act of its name for each other type. -/
def Clause.SentenceType.force : Clause.SentenceType → Mood.Illocutionary
  | .declarative => .declarative
  | .polar | .alternative | .constituent => .interrogative
  | .imperative => .imperative
  | .exclamative => .exclamative
  | .promissive => .promissive

/-- Every force is the conventional force of some sentence type. -/
theorem Clause.SentenceType.force_surjective : Function.Surjective Clause.SentenceType.force := by
  decide

/-- A sentence type asks iff it is interrogative. -/
theorem Clause.SentenceType.force_eq_interrogative_iff (t : Clause.SentenceType) :
    t.force = .interrogative ↔ t.IsInterrogative := by
  cases t <;> simp [Clause.SentenceType.force, Clause.SentenceType.IsInterrogative]
