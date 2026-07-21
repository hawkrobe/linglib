/-!
# Presupposition trigger types

Classification of presupposition triggers by hosting lexical class, the
consensus inventory of the projection literature (cf. [zeevat-1992],
[tonhauser-beaver-roberts-simons-2013]). Fragment lexical entries carry a
`PresupTrigger` value as theory-neutral metadata; orthogonal classifications
of the same inventory are the projection classes of
`Semantics.Presupposition.ProjectiveContent` and the soft/hard distinction in
`Semantics.Verb`.
-/

namespace Semantics.Presupposition.TriggerTypology

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

end Semantics.Presupposition.TriggerTypology
