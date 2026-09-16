/-!
# Presupposition trigger types

Classification of presupposition triggers by hosting lexical class, the
consensus inventory of the projection literature (cf. [zeevat-1992],
[tonhauser-beaver-roberts-simons-2013]). Fragment lexical entries carry a
`PresupTrigger` value as theory-neutral metadata; orthogonal classifications
of the same inventory are the projection classes of
[tonhauser-beaver-roberts-simons-2013] in `Studies/TonhauserEtAl2013`. The
hard/soft split of [abusch-2010] is `TriggerType`, and [karttunen-1973]'s
plug/hole/filter classification of what a predicate does with its
complement's presuppositions is `ProjectionBehavior`; a verb entry's trigger
type is derived (`Verb.triggerType`).

## References

* [zeevat-1992]
* [tonhauser-beaver-roberts-simons-2013]
* [abusch-2010]
* [karttunen-1973]
* [nadathur-2023-implicatives]
-/

namespace Presupposition

/-- The kind of presupposition trigger a predicate is, the hard/soft classification of
[abusch-2010]: hard triggers always project (*too*, *again*, *also*), soft triggers project
context-sensitively (*stop*, *know*), and an implicative presupposes a prerequisite. -/
inductive TriggerType where
  /-- Projective in every context. -/
  | hardTrigger
  /-- A factive or change-of-state trigger, locally accommodatable. -/
  | softTrigger
  /-- An implicative, presupposing its causal prerequisite ([nadathur-2023-implicatives]). -/
  | prerequisiteSoft
  deriving DecidableEq, Repr

/-- Is this trigger locally accommodatable (soft)?
    Both factive and prerequisite triggers are soft. -/
def TriggerType.isSoft : TriggerType → Bool
  | .hardTrigger => false
  | .softTrigger => true
  | .prerequisiteSoft => true

/--
Complement presupposition projection behavior ([karttunen-1973]).

Orthogonal to `TriggerType` (whether the verb *triggers* presuppositions):
this classifies what the verb does with presuppositions *of its complement*.

- `plug`: blocks all complement presuppositions (*say*, *tell*, *promise*)
- `hole`: lets all complement presuppositions project (*know*, *regret*, *stop*)
- `filter`: conditionally cancels some complement presuppositions (*if...then*, *and*, *or*)
-/
inductive ProjectionBehavior where
  | plug    -- Blocks complement presuppositions
  | hole    -- Passes complement presuppositions through
  | filter  -- Conditionally cancels complement presuppositions
  deriving DecidableEq, Repr

end Presupposition


namespace Presupposition.TriggerTypology

/-- Presupposition trigger classes, by hosting lexical item. -/
inductive PresupTrigger where
  /-- Definite descriptions: "the X" presupposes X exists and is unique -/
  | definite
  /-- Factive predicates: "know/regret that P" presupposes P -/
  | factive
  /-- Change-of-state predicates: "stop/start V-ing" presuppose a prior state -/
  | changeOfState
  /-- Repetitive iteratives: "again" presupposes a prior occurrence.
      An intervening ¬P interval (P-then-¬P-then-P-again) is presupposed
      only for stative hosts in competition with the continuative;
      eventive *again* (*John won again*) requires precedence only
      (cf. [von-stechow-1996]). English *again*, German *wieder*,
      Mandarin *you* 又, Cantonese *jau*. -/
  | iterative
  /-- Continuatives: "still" presuppose **uninterrupted** continuation
      of P throughout an interval up to and including the reference time.
      Distinct from `.iterative` (interruption presupposed only for
      statives) and from `.changeOfState` (which involves a polarity
      flip). English *still*, Mandarin *reng* 仍 / *hai* 还,
      Cantonese *zung* 仲. Cf. [ippolito-2007] on *still* vs *again*. -/
  | continuative
  /-- Additives: "too/also" presuppose that a distinct salient alternative
      satisfies the predicate — the paradigm anaphoric trigger
      ([kripke-2009]). English *too*, German *auch*, Mandarin *ye* 也. -/
  | additive
  /-- Exclusives: "only P" presupposes its prejacent P.
      English *only*, Mandarin *jiu* 就. -/
  | exclusive
  /-- Contrastives: "instead"-type particles presuppose a contextually
      salient contrary expectation. Mandarin *fan'er* 反而 / *er* 而. -/
  | contrastive
  /-- Cleft constructions: "It was X that..." presupposes existence -/
  | cleft
  /-- Aspectual predicates: "finish", "continue" presuppose event structure -/
  | aspectual
  deriving DecidableEq, Repr

end Presupposition.TriggerTypology
