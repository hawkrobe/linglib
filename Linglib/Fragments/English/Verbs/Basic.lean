module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Voice.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Morphology.Word.Basic
public import Linglib.Fragments.English.Inflection
public import Linglib.Fragments.English.Adpositions

/-!
# English verbs

This file defines the English verb entry and the simplest verbs. An entry extends the
cross-linguistic `Verb`, with its argument frames, aspectual and semantic class, presupposition,
causation and attitude facets, by the four inflected forms, and `Verb.realize` reads a cell
while `Verb.mkRegular` derives the forms of a regular verb by the spelling rules of
`English.Inflection`. The verbs here are the plain intransitives, transitives and ditransitives
that the studies reach for first, *sleep*, *kick*, *give* and the like, and a few verbs of
consumption and creation; the other classes are in the sibling files and `Verbs/Inventory.lean`
lists them all. A citation form with several entries is a polysemous lexeme told apart by
`senseTag`. An entry's `levinClasses` are the classes whose member lists in Levin's book carry
its citation form, less the classes that list the form in a sense the entry is not, and
`scripts/check_levin_classes.py` checks the entries against the lists.

## References

* [levin-1993]
* [bruening-2021]
* [fillmore-1986]
* [levin-hovav-1995]
-/

@[expose] public section

open Morphology (Word Features)

namespace English.Verbs

open ArgumentStructure Aspect Degree
open English.Inflection

/-! ### The entry type -/

/--
A complete English lexical entry for a verb.

Extends the cross-linguistic `Verb` (argument structure, semantic class,
compositional links) with English-specific inflectional morphology.
-/
structure Verb extends _root_.Verb where
  /-- Third person singular present (for agreement) -/
  form3sg : String
  /-- Past tense form -/
  formPast : String
  /-- Past participle (for passives, perfects) -/
  formPastPart : String
  /-- Present participle / gerund -/
  formPresPart : String
  deriving BEq

/-- Construct a regular verb entry, computing the inflected forms from the citation form
    by the regular spelling rules.

    Usage:
    ```
    def kick : Verb := .mkRegular {
      form := "kick", valency := .ofFrame ArgumentFrame.np }
    ``` -/
def Verb.mkRegular (core : _root_.Verb) : Verb :=
  { toVerb := core
    form3sg := suffixS core.form
    formPast := suffixEd core.form
    formPastPart := suffixEd core.form
    formPresPart := suffixIng core.form }

/-- Every inflected form follows the regular spelling rules from the citation form. -/
def Verb.IsRegular (v : Verb) : Prop :=
  v.form3sg = suffixS v.form ∧ v.formPast = suffixEd v.form ∧
    v.formPastPart = suffixEd v.form ∧ v.formPresPart = suffixIng v.form

instance (v : Verb) : Decidable v.IsRegular := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A regular entry is regular. -/
theorem Verb.mkRegular_isRegular (core : _root_.Verb) : (Verb.mkRegular core).IsRegular :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The inflectional cells of an entry. -/
inductive Verb.Cell where
  | base
  | thirdSg
  | presentPlural
  | past
  | pastParticiple
  | presentParticiple
  deriving DecidableEq, Repr, Fintype

/-- The form an entry realizes in each cell. -/
def Verb.realize (e : Verb) : Verb.Cell → String
  | .base => e.form
  | .thirdSg => e.form3sg
  | .presentPlural => e.form
  | .past => e.formPast
  | .pastParticiple => e.formPastPart
  | .presentParticiple => e.formPresPart

/-! ### Simple -/

/-- "sleep" — intransitive, no presupposition -/
def sleep : Verb where
  form := "sleep"
  form3sg := "sleeps"
  formPast := "slept"
  formPastPart := "slept"
  formPresPart := "sleeping"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.fit, .snooze}

/-- "sneeze" — intransitive -/
def sneeze : Verb := .mkRegular {
  form := "sneeze"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  levinClasses := {LevinClass.hiccup, .nonverbalExpression} }

/-- "run" — intransitive, no presupposition -/
def run : Verb where
  form := "run"
  form3sg := "runs"
  formPast := "ran"
  formPastPart := "run"
  formPresPart := "running"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.unaccusative, [0]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  root := { content := {
    force := {.moderate}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.meander, .prepare, .run, .swarm}

/-- "dance" — intransitive activity -/
def dance : Verb := .mkRegular {
  form := "dance"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .performance, .waltz} }

/-- "arrive" — unaccusative intransitive -/
def arrive : Verb := .mkRegular {
  form := "arrive"
  valency := .ofFrame ArgumentFrame.unaccusative [some achievementSubjectProfile]
  passivizable := false
  vendlerClass := some .achievement
  direction := some .goal
  levinClasses := {LevinClass.inherentlyDirectedMotion} }

/-- "come" — Levin 51.1 inherently directed motion, like `arrive`. -/
def come : Verb where
  form := "come"
  form3sg := "comes"
  formPast := "came"
  formPastPart := "come"
  formPresPart := "coming"
  valency := .ofFrame ArgumentFrame.unaccusative
  passivizable := false
  vendlerClass := some .achievement
  direction := some .goal
  levinClasses := {LevinClass.appear, .inherentlyDirectedMotion}

/-- "go" — Levin 51.1 inherently directed motion, suppletive in the past. -/
def go : Verb where
  form := "go"
  form3sg := "goes"
  formPast := "went"
  formPastPart := "gone"
  formPresPart := "going"
  valency := .ofFrame ArgumentFrame.unaccusative
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.inherentlyDirectedMotion}
  levinExcluded := {LevinClass.meander}

/-- In *run into the room* a bounded goal phrase makes a verb of manner of motion directed and
telic, while *run behind the house* leaves it as it is, and so does any path phrase *sleep*, which
selects none. -/
example : (run.withPath Adposition.into).direction = some .goal ∧
    (run.withPath Adposition.into).vendlerClass = some .accomplishment ∧
    run.withPath Adposition.behind = run.toVerb ∧ sleep.withPath Adposition.into = sleep.toVerb :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- *Dance* says nothing of a path, *run* displaces its subject without a direction, and *arrive*
lexicalizes a goal ([levin-hovav-1995] p. 147). -/
example : dance.direction = none ∧ run.direction = some .place ∧ arrive.direction = some .goal :=
  ⟨rfl, rfl, rfl⟩

/-- "eat" — transitive, implicit object is indefinite ("Have you eaten?") -/
def eat : Verb where
  form := "eat"
  form3sg := "eats"
  formPast := "ate"
  formPastPart := "eaten"
  formPresPart := "eating"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
    [some accomplishmentSubjectProfile, some consumptionObject]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.low, .moderate}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.eat}

/-- "kick" — transitive -/
def kick : Verb := .mkRegular {
  form := "kick"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
    [some accomplishmentSubjectProfile, some contactObject, none, none]
  vendlerClass := some .activity
  root := { content := {
    force := {.moderate, .high}
    forceDirection := {.unidirectional}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.bodyInternalMotion, .carry, .crane, .hit, .split, .throw} }

/-- "aim" — with an *at*-phrase, and transitive with one -/
def aim : Verb := .mkRegular {
  form := "aim"
  valency := .of
    [(ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.at_), [0, 2, 1])] }

/-- "give" — ditransitive, alternates DOC/PP.
    Implicit goal is definite ([fillmore-1986]: pragmatically recoverable).
    Neither object can be implicit alone. -/
def give : Verb where
  form := "give"
  form3sg := "gives"
  formPast := "gave"
  formPastPart := "given"
  formPresPart := "giving"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (⟨some .nominal, [.implicit (some .indef), .adpositional]⟩, [0, 2, 1]),
     (⟨some .nominal, [.nominal, .implicit (some .def)]⟩, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "put" — locative -/
def put : Verb where
  form := "put"
  form3sg := "puts"
  formPast := "put"
  formPastPart := "put"
  formPresPart := "putting"
  valency := .ofFrame ArgumentFrame.np_pp
  vendlerClass := some .achievement
  levinClasses := {LevinClass.put}

/-- "weigh" — measure predicate selecting for mass/weight. -/
def weigh : Verb := .mkRegular {
  form := "weigh"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.register} }

/-- "cover" — motion/extent predicate selecting for distance. -/
def cover : Verb := .mkRegular {
  form := "cover"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.contiguousLocation, .fill} }

/-- "measure" — general measurement predicate. -/
def measure : Verb := .mkRegular {
  form := "measure"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.register} }

/-- "buy" — irregular transitive -/
def buy : Verb where
  form := "buy"
  form3sg := "buys"
  formPast := "bought"
  formPastPart := "bought"
  formPresPart := "buying"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
    [some possessionTransfer.subjectProfile, none, none]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get}

/-- "meet" — irregular transitive -/
def meet : Verb where
  form := "meet"
  form3sg := "meets"
  formPast := "met"
  formPastPart := "met"
  formPresPart := "meeting"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.objectDrop (some .reciprocal), [0, 1])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.contiguousLocation, .meet}

/-- "set" — irregular; the base, past and past participle forms coincide. -/
def set_ : Verb where
  form := "set"
  form3sg := "sets"
  formPast := "set"
  formPastPart := "set"
  formPresPart := "setting"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.braid, .imageImpression, .prepare, .put}

/-- "clarify" — regular transitive. -/
def clarify : Verb where
  form := "clarify"
  form3sg := "clarifies"
  formPast := "clarified"
  formPastPart := "clarified"
  formPresPart := "clarifying"
  valency := .ofFrame ArgumentFrame.np

/-- "sell" — change of possession, alternates DOC/PP.
    Implicit DO is definite; implicit goal is indefinite. -/
def sell : Verb where
  form := "sell"
  form3sg := "sells"
  formPast := "sold"
  formPastPart := "sold"
  formPresPart := "selling"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (⟨some .nominal, [.implicit (some .def), .adpositional]⟩, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
    [some possessionTransfer.subjectProfile, none, none]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "leave" — transitive (also used intransitively with argument drop) -/
def leave : Verb where
  form := "leave"
  form3sg := "leaves"
  formPast := "left"
  formPastPart := "left"
  formPresPart := "leaving"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.fulfilling, .futureHaving, .get, .inherentlyDirectedMotion, .keep,
    .leave}

/-- "see" — transitive; factive with a finite-clause complement -/
def see : Verb where
  form := "see"
  form3sg := "sees"
  formPast := "saw"
  formPastPart := "seen"
  formPresPart := "seeing"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.finiteClause, [0, 1])]
    [some perception.subjectProfile, none]
  vendlerClass := some .state
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.characterize, .see}

/-! ### Other -/

/-- "devour" — transitive, no presupposition -/
def devour : Verb := .mkRegular {
  form := "devour"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.moderate, .high}
    agentControl := {.neutral}
  } }
  levinClasses := {LevinClass.devour} }

/-- "drink" — Levin 39.1 Eat verbs. -/
def drink : Verb where
  form := "drink"
  form3sg := "drinks"
  formPast := "drank"
  formPastPart := "drunk"
  formPresPart := "drinking"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.eat}

/-- "read" — Levin 14 Learn verbs, with learn and study; also listed among the verbs of
    transfer of a message (37.1) and the register verbs (54.1). -/
def read : Verb where
  form := "read"
  form3sg := "reads"
  formPast := "read"
  formPastPart := "read"
  formPresPart := "reading"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .incremental
  levinClasses := {LevinClass.learn, .register, .transferOfMessage}

/-- "build" — creation verb, strictly incremental theme.
    Base transitive that productively takes DOC ("build us a house"). -/
def build : Verb where
  form := "build"
  form3sg := "builds"
  formPast := "built"
  formPastPart := "built"
  formPresPart := "building"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.outOf), [0, 1, 3]),
     (ArgumentFrame.np_pp (some Adpositions.into), [0, 3, 1])]
    [some accomplishmentSubjectProfile, some creationObject, none, none]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.build}

/-- "write" — Levin 25.2 Scribble verbs, cross-listed with the build verbs;
    creation verb, strictly incremental theme.
    Alternates DOC/PP. Implicit DO in both frames (indefinite).
    Uniquely allows implicit DO in both DOC and PP ([bruening-2021]). -/
def write : Verb where
  form := "write"
  form3sg := "writes"
  formPast := "wrote"
  formPastPart := "written"
  formPresPart := "writing"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, [0, 2, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.performance, .scribble, .transferOfMessage}

/-- "sweep" — motion + sustained contact, variable agentivity (default sense). -/
def sweep : Verb where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
    [some wipeManner.subjectProfile, none, none]
  vendlerClass := some .activity
  passivizable := true
  root := { content := {
    force := {.low, .moderate}
    forceDirection := {.unidirectional}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.entitySpecificModeOfBeing, .funnel, .meander, .run, .wipeManner}

/-- "sweep" instrument sense — obligatorily agentive, broom lexicalized. -/
def sweep_instr : Verb where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 3])]
    [some wipeInstrument.subjectProfile, none, none]
  vendlerClass := some .activity
  passivizable := true
  senseTag := .instrumental
  root := { content := {
    force := {.low, .moderate}
    forceDirection := {.unidirectional}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.entitySpecificModeOfBeing, .funnel, .meander, .run, .wipeManner}

/-! ### Words -/

/-- The morphosyntactic features of an inflectional cell. -/
def Verb.Cell.features : Verb.Cell → Features
  | .base => Features.of (verbForm := some .Inf)
  | .thirdSg => Features.of (number := some .singular) (person := some .third)
      (voice := some .Act) (verbForm := some .Fin) (tense := some .Pres)
  | .presentPlural => Features.of (number := some .plural) (tense := some .Pres)
  | .past => Features.of (verbForm := some .Fin) (voice := some .Act) (tense := some .Past)
  | .pastParticiple => Features.of (verbForm := some .Part)
  | .presentParticiple => Features.of (verbForm := some .Part)

/-- The entry's form in a cell as a `Word`, with the cell's features. -/
def Verb.toWord (v : Verb) (c : Verb.Cell) : Word :=
  { form := v.realize c, cat := .VERB, features := c.features }

/-- The past participle in passive voice, the same form as `toWord .pastParticiple` marked
passive. -/
def Verb.passiveParticiple (v : Verb) : Word :=
  { form := v.formPastPart, cat := .VERB,
    features := Features.of (verbForm := some .Part) (voice := some .Pass) }

end English.Verbs
