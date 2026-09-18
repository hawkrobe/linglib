/-!
# Presupposition triggers

This file defines the classifications of a presupposition trigger, an expression whose use
takes some proposition for granted. A trigger belongs to a class by the kind of expression that
hosts it (`Trigger`), the consensus inventory of the projection literature after Zeevat and
after Tonhauser, Beaver, Roberts and Simons. Abusch divides triggers into hard ones, whose
presupposition always projects, and soft ones, whose presupposition can be suspended
(`TriggerType`). Karttunen divides the factive predicates into true factives and semi-factives
(`Factivity`), and classifies a predicate as a plug, a hole or a filter by what it does with the
presuppositions of its complement (`ProjectionBehavior`). A verb's entry records its factivity
and projection behavior, and its trigger type is derived (`Verb.triggerType?`); an adverb,
particle or affix that triggers a presupposition is a `TriggerItem`.

## References

* [zeevat-1992]
* [tonhauser-beaver-roberts-simons-2013]
* [abusch-2010]
* [karttunen-1971b]
* [karttunen-1973]
* [nadathur-2023-implicatives]
* [von-stechow-1996]
* [ippolito-2007]
* [kripke-2009]
-/

namespace Presupposition

/-- The kind of presupposition trigger a predicate is, in the hard/soft classification of
[abusch-2010]. Hard triggers always project (*too*, *again*, *also*), soft triggers project
context-sensitively (*stop*, *know*), and an implicative presupposes a prerequisite. -/
inductive TriggerType where
  /-- Projective in every context. -/
  | hard
  /-- A factive or change-of-state trigger, locally accommodatable. -/
  | soft
  /-- An implicative, presupposing its causal prerequisite ([nadathur-2023-implicatives]). -/
  | prerequisite
  deriving DecidableEq, Repr

/-- The factivity class of a predicate ([karttunen-1971b]). -/
inductive Factivity where
  /-- A true factive such as *regret* or *forget*, whose complement follows even from the
  possibility of the sentence. -/
  | full
  /-- A semi-factive such as *know* or *discover*, whose complement follows from the sentence
  and its negation only. -/
  | semi
  deriving DecidableEq, Repr

/-- What a predicate does with the presuppositions of its complement ([karttunen-1973]). The
classification is orthogonal to `TriggerType`, which says whether the predicate itself triggers
a presupposition. -/
inductive ProjectionBehavior where
  /-- A plug blocks every presupposition of its complement (*say*, *tell*, *promise*). -/
  | plug
  /-- A hole lets every presupposition of its complement project (*know*, *regret*, *stop*). -/
  | hole
  /-- A filter cancels some presuppositions of its complement under a condition (*if ... then*,
  *and*, *or*). -/
  | filter
  deriving DecidableEq, Repr

/-- The class of a presupposition trigger, by the kind of expression that hosts it. -/
inductive Trigger where
  /-- A definite description *the X* presupposes that a unique X exists. -/
  | definite
  /-- A factive predicate, *know* or *regret that p*, presupposes `p`. -/
  | factive
  /-- A change-of-state expression, *stop*, *start* or *no longer*, presupposes the prior state. -/
  | changeOfState
  /-- A repetitive iterative, *again*, presupposes a prior occurrence. An intervening interval
  without the eventuality is presupposed only for stative hosts, in competition with the
  continuative; eventive *again* (*John won again*) requires precedence only
  ([von-stechow-1996]). -/
  | iterative
  /-- A continuative, *still*, presupposes that the state has held without interruption up to
  the reference time ([ippolito-2007]). -/
  | continuative
  /-- An additive, *too* or *also*, presupposes that a distinct salient alternative satisfies
  the predicate, and is the paradigm anaphoric trigger ([kripke-2009]). -/
  | additive
  /-- An exclusive, *only p*, presupposes its prejacent `p`. -/
  | exclusive
  /-- A contrastive, *instead*, presupposes that a salient alternative is false. -/
  | contrastive
  /-- A cleft *it was X that ...* presupposes existence. -/
  | cleft
  /-- An aspectual predicate, *finish* or *continue*, presupposes event structure. -/
  | aspectual
  deriving DecidableEq, Repr

/-- A presupposition trigger outside the verbal lexicon, an adverb, particle or affix, with its
trigger class. A verb's presuppositions are recorded on its `Verb` entry. -/
structure TriggerItem where
  /-- The citation form, a romanization where the language is not written in Latin script. -/
  form : String
  /-- The native-script form of a romanized item. -/
  script : Option String := none
  /-- The trigger class. -/
  trigger : Trigger
  deriving DecidableEq, Repr

end Presupposition
