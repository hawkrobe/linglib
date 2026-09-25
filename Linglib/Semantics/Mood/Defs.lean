/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct
public import Mathlib.Tactic.DeriveFintype

/-!
# Mood categories

This file defines grammatical mood and Portner's classification of mood-bearing categories.
Grammatical mood is the indicative or subjunctive morphology of the verb, and it crosses freely
with the sentence type and the force of the clause, as Holmberg observes: a polar question is
interrogative and indicative, while the Spanish deliberative *¿Que duerma?* is interrogative
and subjunctive. Portner classifies each mood-bearing category, the illocutionary forces of
`Discourse.SpeechAct.Force` among them, by the coordinate of the mood state it operates on.

## Main declarations

* `Grammatical`, `SubjunctiveType`: verb-morphological mood.
* `Component`, `HasTarget`: Portner's classification by the coordinate of the mood state.

## References

* [holmberg-2016]
* [portner-2018]
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

/-- The targets of the illocutionary forces, Portner's sentence moods. The promissive and the
exclamative are linglib extensions, and the exclamative assignment is a conjectural
placeholder. -/
instance : HasTarget Discourse.SpeechAct.Force where
  target
    | .declarative   => .informational
    | .imperative    => .preferential
    | .promissive    => .preferential
    | .interrogative => .inquisitive
    | .exclamative   => .informational

end Mood
