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
      form := "kick", frames := [ArgumentFrame.np] }
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
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.fit, .snooze}

/-- "run" — intransitive, no presupposition -/
def run : Verb where
  form := "run"
  form3sg := "runs"
  formPast := "ran"
  formPastPart := "run"
  formPresPart := "running"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative]
  subjectEntailments := some activitySubjectProfile
  passivizable := false
  vendlerClass := some .activity
  root := { content := {
    force := {.moderate}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.meander, .prepare, .run, .swarm}

/-- "dance" — intransitive activity -/
def dance : Verb := .mkRegular {
  form := "dance"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity }

/-- "arrive" — unaccusative intransitive -/
def arrive : Verb := .mkRegular {
  form := "arrive"
  frames := [ArgumentFrame.unaccusative]
  subjectEntailments := some achievementSubjectProfile
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.inherentlyDirectedMotion} }

/-- "come" — Levin 51.1 inherently directed motion, like `arrive`. -/
def come : Verb where
  form := "come"
  form3sg := "comes"
  formPast := "came"
  formPastPart := "come"
  formPresPart := "coming"
  frames := [ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appear, .inherentlyDirectedMotion}

/-- "go" — Levin 51.1 inherently directed motion, suppletive in the past. -/
def go : Verb where
  form := "go"
  form3sg := "goes"
  formPast := "went"
  formPastPart := "gone"
  formPresPart := "going"
  frames := [ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.inherentlyDirectedMotion}

/-- "eat" — transitive, implicit object is indefinite ("Have you eaten?") -/
def eat : Verb where
  form := "eat"
  form3sg := "eats"
  formPast := "ate"
  formPastPart := "eaten"
  formPresPart := "eating"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef),
    ArgumentFrame.pp (some Adpositions.at_)]
  subjectEntailments := some accomplishmentSubjectProfile
  objectEntailments := some consumptionObject
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
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  subjectEntailments := some accomplishmentSubjectProfile
  objectEntailments := some contactObject
  vendlerClass := some .activity
  root := { content := {
    force := {.moderate, .high}
    direction := {.unidirectional}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.bodyInternalMotion, .carry, .crane, .hit, .split, .throw} }

/-- "give" — ditransitive, alternates DOC/PP.
    Implicit goal is definite ([fillmore-1986]: pragmatically recoverable).
    Neither object can be implicit alone. -/
def give : Verb where
  form := "give"
  form3sg := "gives"
  formPast := "gave"
  formPastPart := "given"
  formPresPart := "giving"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .indef), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "put" — locative -/
def put : Verb where
  form := "put"
  form3sg := "puts"
  formPast := "put"
  formPastPart := "put"
  formPresPart := "putting"
  frames := [ArgumentFrame.np_pp]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.put}

/-- "weigh" — measure predicate selecting for mass/weight. -/
def weigh : Verb := .mkRegular {
  form := "weigh"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.register} }

/-- "cover" — motion/extent predicate selecting for distance. -/
def cover : Verb := .mkRegular {
  form := "cover"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.contiguousLocation, .fill} }

/-- "measure" — general measurement predicate. -/
def measure : Verb := .mkRegular {
  form := "measure"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.register} }

/-- "buy" — irregular transitive -/
def buy : Verb where
  form := "buy"
  form3sg := "buys"
  formPast := "bought"
  formPastPart := "bought"
  formPresPart := "buying"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.for_), ArgumentFrame.np_np]
  subjectEntailments := some possessionTransfer.subjectProfile
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get}

/-- "meet" — irregular transitive -/
def meet : Verb where
  form := "meet"
  form3sg := "meets"
  formPast := "met"
  formPastPart := "met"
  formPresPart := "meeting"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .reciprocal)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.contiguousLocation, .meet}

/-- "set" — irregular; the base, past and past participle forms coincide. -/
def set_ : Verb where
  form := "set"
  form3sg := "sets"
  formPast := "set"
  formPastPart := "set"
  formPresPart := "setting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.braid, .imageImpression, .prepare, .put}

/-- "clarify" — regular transitive. -/
def clarify : Verb where
  form := "clarify"
  form3sg := "clarifies"
  formPast := "clarified"
  formPastPart := "clarified"
  formPresPart := "clarifying"
  frames := [ArgumentFrame.np]

/-- "sell" — change of possession, alternates DOC/PP.
    Implicit DO is definite; implicit goal is indefinite. -/
def sell : Verb where
  form := "sell"
  form3sg := "sells"
  formPast := "sold"
  formPastPart := "sold"
  formPresPart := "selling"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .def), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  subjectEntailments := some possessionTransfer.subjectProfile
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "leave" — transitive (also used intransitively with argument drop) -/
def leave : Verb where
  form := "leave"
  form3sg := "leaves"
  formPast := "left"
  formPastPart := "left"
  formPresPart := "leaving"
  frames := [ArgumentFrame.np]
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
  frames := [ArgumentFrame.np, ArgumentFrame.finiteClause]
  subjectEntailments := some perception.subjectProfile
  vendlerClass := some .state
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.characterize, .see}

/-! ### Other -/

/-- "devour" — transitive, no presupposition -/
def devour : Verb := .mkRegular {
  form := "devour"
  frames := [ArgumentFrame.np]
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
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef),
    ArgumentFrame.pp (some Adpositions.at_)]
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
  frames := [ArgumentFrame.np]
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
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef),
    ArgumentFrame.np_pp (some Adpositions.for_), ArgumentFrame.np_np,
    ArgumentFrame.np_pp (some Adpositions.outOf), ArgumentFrame.np_pp (some Adpositions.into)]
  subjectEntailments := some accomplishmentSubjectProfile
  objectEntailments := some creationObject
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
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩, ArgumentFrame.objectDrop (some .indef)]
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
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.objectDrop (some .indef),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  subjectEntailments := some wipeManner.subjectProfile
  passivizable := true
  root := { content := {
    force := {.low, .moderate}
    direction := {.unidirectional}
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
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.objectDrop (some .indef),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  subjectEntailments := some wipeInstrument.subjectProfile
  passivizable := true
  senseTag := .instrumental
  root := { content := {
    force := {.low, .moderate}
    direction := {.unidirectional}
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
