module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Voice.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Morphology.Word.Basic
public import Linglib.Fragments.English.Inflection
public import Linglib.Fragments.English.Adposition

@[expose] public section

open Morphology (Word Features)

/-!
# English verbs

The English verb lexicon: each entry extends the cross-linguistic `Verb` (argument frames,
aspectual and semantic class, presupposition, causation and attitude facets) with the four
inflected forms, `Verb.realize` reading a cell and `Verb.mkRegular` deriving the forms of a
regular verb by the spelling rules of `Inflection.lean`. Entries are grouped by the
[levin-1993] class they carry, then by the paper whose classification they record; the
inventory `verbs` lists them all. English has two voices, the active and a periphrastic
passive, the auxiliary *be* with the past participle, the patient the subject and the agent
demoted to an optional *by*-phrase; `voices` lists them.

## Implementation notes

A citation form with several entries is a polysemous lexeme, told apart by `senseTag`
(*forget* the implicative and *forget* the rogative, *sweep* with and without an instrument
frame). An entry's `levinClasses` are the classes whose member lists in [levin-1993] Part II
carry its citation form (`LevinClass.members`), less the classes that list the form in a sense
the entry is not (`levinExcluded`); `scripts/check_levin_classes.py` checks the entries against
the lists. A verb Levin does not list carries none even when a paper groups it with a class.
Where the sources describe a reflex as dialect-variable or optional, the docstring says so.

## References

* [bruening-2021]
* [dayal-2025]
* [degen-tonhauser-2022]
* [embick-2009]
* [fillmore-1986]
* [fusco-sgrizzi-2026]
* [grano-2024]
* [karttunen-1971]
* [kennedy-2007]
* [kim-2024]
* [klecha-2016]
* [landau-2015]
* [levin-1993]
* [levin-2026]
* [majid-boster-bowerman-2008]
* [martin-rose-nichols-2025]
* [nadathur-lauer-2020]
* [rappaport-hovav-2014]
* [smith-1997]
* [solstad-bott-2024]
* [spalek-mcnally-2026]
* [storment-2026]
* [tham-2025]
-/

namespace English

open ArgumentStructure Aspect Degree

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

/-! ### Factive / Semifactive -/

/-- "know" — factive, presupposes complement is true -/
def know : Verb where
  form := "know"
  form3sg := "knows"
  formPast := "knew"
  formPastPart := "known"
  formPresPart := "knowing"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  complementSig := some .mono
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture}

/-- "regret" — emotive factive, presupposes complement is true -/
def regret : Verb where
  form := "regret"
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.preferential (.degreeComparison .negative))
  factivity := some .full
  levinClasses := {LevinClass.admire}

/-- "realize" — factive, presupposes complement is true -/
def realize : Verb := .mkRegular {
  form := "realize"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-- "discover" — semi-factive, weaker projection -/
def discover : Verb := .mkRegular {
  form := "discover"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture, .sight} }

/-- "notice" — semi-factive -/
def notice : Verb := .mkRegular {
  form := "notice"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  levinClasses := {LevinClass.see} }

/-! ### Change of State -/

/-- "stop" — phasal cessation, presupposes activity was happening -/
def stop : Verb where
  form := "stop"
  form3sg := "stops"
  formPast := "stopped"
  formPastPart := "stopped"
  formPresPart := "stopping"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  phasal := some .cessation
  levinClasses := {LevinClass.begin, .lodge}

/-- "quit" — phasal cessation -/
def quit : Verb where
  form := "quit"
  form3sg := "quits"
  formPast := "quit"
  formPastPart := "quit"
  formPresPart := "quitting"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .cessation
  levinClasses := {LevinClass.complete}

/-- "start" — phasal inception, presupposes activity wasn't happening -/
def start : Verb := .mkRegular {
  form := "start"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception
  levinClasses := {LevinClass.begin} }

/-- "begin" — phasal inception -/
def begin_ : Verb where
  form := "begin"
  form3sg := "begins"
  formPast := "began"
  formPastPart := "begun"
  formPresPart := "beginning"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception
  levinClasses := {LevinClass.begin}

/-- "continue" — phasal continuation, presupposes activity was happening -/
def continue_ : Verb := .mkRegular {
  form := "continue"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation
  levinClasses := {LevinClass.begin} }

/-- "keep" — phasal continuation -/
def keep : Verb where
  form := "keep"
  form3sg := "keeps"
  formPast := "kept"
  formPastPart := "kept"
  formPresPart := "keeping"
  frames := [ArgumentFrame.gerund, ArgumentFrame.np, ArgumentFrame.unaccusative]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation
  levinClasses := {LevinClass.begin, .get, .keep}

/-! ### Implicative / Control -/

/-- "manage" — a positive implicative; "managed to VP" entails "VP", and on the traditional
    analysis the agentive subject controls the complement.
    -/
def manage : Verb := .mkRegular {
  form := "manage"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  implicative := some .positive }

/-- "fail" — a negative implicative; "failed to VP" entails "not VP". -/
def fail : Verb := .mkRegular {
  form := "fail"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .negative }

/-- "try" — subject control, no entailment -/
def try_ : Verb where
  form := "try"
  form3sg := "tries"
  formPast := "tried"
  formPastPart := "tried"
  formPresPart := "trying"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.amuse}

/-- "persuade" — object control, "persuade X to VP" with X the agent of VP. A psychological
    attitude verb whose object comes to form an intention; it projects the AUTHOR coordinate,
    so control is obligatorily *de se* ([landau-2015] table (36)). -/
def persuade : Verb := .mkRegular {
  form := "persuade"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "promise" — subject control across an object, "promise X to VP". A desiderative attitude
    verb whose subject commits to a future action; [landau-2015] (5c) classifies it as
    desiderative, hence logophoric control. -/
def promise : Verb := .mkRegular {
  form := "promise"
  frames := [ArgumentFrame.infinitival,
    ArgumentFrame.np_np, ArgumentFrame.np_pp (some Adpositions.to_)]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.futureHaving} }

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : Verb := .mkRegular {
  form := "remember"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive
  levinClasses := {LevinClass.characterize} }

/-- "forget" — negative implicative with infinitival -/
def forget : Verb where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .negative

/-- "neglect" — negative implicative, listed with *forget* and *fail* among
    [karttunen-1971]'s negative implicatives: neglecting to lock the door
    entails not locking it. -/
def neglect : Verb := .mkRegular {
  form := "neglect"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .negative }

/-! ### Doxastic Attitude -/

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : Verb := .mkRegular {
  form := "believe"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  levinClasses := {LevinClass.declare} }

/-- "think" — doxastic attitude verb -/
def think : Verb where
  form := "think"
  form3sg := "thinks"
  formPast := "thought"
  formPastPart := "thought"
  formPresPart := "thinking"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  levinClasses := {LevinClass.declare}

/-! ### Preferential Attitude -/

/-- "want" — preferential attitude verb with infinitival complement -/
def want : Verb := .mkRegular {
  form := "want"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.appoint, .want} }

/-- "intend" — intention-reporting attitude verb ([grano-2024]).
    Primary frame: infinitival with subject control ("intend to leave").
    Alternate frame: for-to non-control ("intend for Ben to come along").
    Rejects indicative complements cross-linguistically: *"Kim intends
    that Sandy leaves." Requires eventuality abstraction (cause* binds
    the complement's event argument). -/
def intend : Verb := .mkRegular {
  form := "intend"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.characterize} }

/-- "decide" — belief/intention hybrid attitude verb ([grano-2024], §6.1).
    Nonfinite complement → intention formation: "Kim decided to quit smoking"
    Finite complement → belief formation: "Kim decided that smoking is harmful"
    The complement type determines the reading, as with Italian *convincere*
    ([fusco-sgrizzi-2026]). -/
def decide_ : Verb := .mkRegular {
  form := "decide"
  frames := [ArgumentFrame.infinitival, ArgumentFrame.finiteClause]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "hope" — preferential attitude verb.
    Primary frame: finite clause ("hope that John leaves").
    Alternate frame: infinitival with subject control ("hope to leave"). -/
def hope : Verb := .mkRegular {
  form := "hope"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.long} }

/-- "pray" — preferential attitude verb, permits future temporal orientation.
    [klecha-2016]: like *hope*, *pray* can take a circumstantial modal base,
    allowing future-oriented readings under past tense morphology.
    Primary frame: finite clause ("pray that God helps").
    Alternate frame: infinitival with subject control ("pray to be saved"). -/
def pray : Verb := .mkRegular {
  form := "pray"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.long} }

/-- "expect" — preferential attitude verb -/
def expect : Verb := .mkRegular {
  form := "expect"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "wish" — preferential attitude verb -/
def wish : Verb where
  form := "wish"
  form3sg := "wishes"
  formPast := "wished"
  formPastPart := "wished"
  formPresPart := "wishing"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClasses := {LevinClass.long}

/-- "fear" — a preferential attitude verb of Class 2, which takes questions. -/
def fear : Verb := .mkRegular {
  form := "fear"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  levinClasses := {LevinClass.admire, .marvel} }

/-- "dread" — a preferential attitude verb of Class 2, which takes questions. -/
def dread : Verb := .mkRegular {
  form := "dread"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  levinClasses := {LevinClass.admire} }

/-- "worry" — preferential attitude verb -/
def worry : Verb where
  form := "worry"
  form3sg := "worries"
  formPast := "worried"
  formPastPart := "worried"
  formPresPart := "worrying"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased)
  levinClasses := {LevinClass.amuse}

/-! ### Raising -/

/-- "seem" — raising verb (no theta role for subject, unaccusative) -/
def seem : Verb := .mkRegular {
  form := "seem"
  frames := [ArgumentFrame.raising]
  readings := [{ frame := ArgumentFrame.raising, control := some .raising }]
  vendlerClass := some .state
  passivizable := false }

/-! ### Causative (Periphrastic) -/

/-- "cause" — counterfactual dependence (necessity semantics) -/
def cause : Verb := .mkRegular {
  form := "cause"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .cause
  levinClasses := {LevinClass.engender} }

/-- "make" — the periphrastic causative asserting a direct sufficient guarantee, which Levin
    does not class (the *make* of 26.1 is the verb of creation and that of 29.3 the dub verb). -/
def make : Verb where
  form := "make"
  form3sg := "makes"
  formPast := "made"
  formPastPart := "made"
  formPresPart := "making"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .make
  levinExcluded := {LevinClass.build, .dub}

/-- "let" — permissive causative (barrier removal) -/
def let_ : Verb where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .achievement
  causative := some .enable

/-- "have" — causative use (directive causation) -/
def have_caus : Verb where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  vendlerClass := some .achievement
  causative := some .make
  senseTag := .causative

/-- "get" — causative use (persuasive causation), which Levin does not class (the *get* of
    13.5.1 is the verb of obtaining). -/
def get_caus : Verb where
  form := "get"
  form3sg := "gets"
  formPast := "got"
  formPastPart := "gotten"
  formPresPart := "getting"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .make
  senseTag := .causative
  levinExcluded := {LevinClass.get}

/-- "force" — coercive causative (overcome resistance) -/
def force : Verb := .mkRegular {
  form := "force"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  projectionBehavior := some .hole
  causative := some .force }

/-- "prevent" — blocking causative (barrier addition).
    "X prevented Y from V-ing" entails the effect did NOT occur
    (¬p in w₀) but would have without X's intervention.
    Its semantics `preventSem` is the blocking dual of the necessity reading
    [nadathur-lauer-2020] give *cause*. -/
def prevent : Verb := .mkRegular {
  form := "prevent"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .objectControl }]
  vendlerClass := some .accomplishment
  projectionBehavior := some .hole
  causative := some .prevent }

/-! ### Lexical Causatives -/

/-- "kill" — Levin 42.1 murder verbs. -/
def kill : Verb := .mkRegular {
  form := "kill"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.murder} }

/-- "break" — Levin 45.1 break verbs, a change in "material integrity" with no specification
    of how the change comes about ([levin-1993]:241). -/
def break_ : Verb where
  form := "break"
  form3sg := "breaks"
  formPast := "broke"
  formPastPart := "broken"
  formPresPart := "breaking"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  root := { content := {
    force := {.moderate, .high}
    -- direction unconstrained: *break* covers snapping (bidirectional),
    -- hammering (omnidirectional), and directed blows (unidirectional)
    patientRobustness := {.moderate, .robust}
    resultGeometry := {.fracture}
    agentControl := {.incompatible, .neutral}
    -- break is unspecified for instrument and object dimensionality
    -- ([majid-boster-bowerman-2008]: Dim 1 low predictability)
  } }
  levinClasses := {LevinClass.appear, .break_, .cheat, .hurt, .split}

/-- "tear" — Levin 45.1 Break Verbs. Contrary-direction separation with force.
    Unlike *break*, *tear* implies a specific directionality (bidirectional /
    pulling apart) and is compatible with careful controlled action.
    Patient restriction: any solid capable of irregular separation.
    [spalek-mcnally-2026] (§3.1–3.2).
    [majid-boster-bowerman-2008]: Dimension 2 — tearing consistently
    distinguished from break/cut across 10/28 languages. -/
def tear_ : Verb where
  form := "tear"
  form3sg := "tears"
  formPast := "tore"
  formPastPart := "torn"
  formPresPart := "tearing"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  causative := some .make
  root := { content := {
    force := {.moderate, .high}
    direction := {.bidirectional, .unidirectional}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.separation}
    agentControl := {.neutral, .compatible}
    instrument := {.hands}
    patientDimensionality := {.twoD}
  } }
  levinClasses := {LevinClass.break_, .run, .split}

/-! ### Physical disturbance change-of-state verbs ([tham-2025]) -/

/-- "crack" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale (contra [rappaport-hovav-2014] two-point
    classification), but allows BOTH telic ("cracked in a minute") and atelic
    ("cracked for two days") readings. Compatible with *completely*, *partially*,
    *badly*. The verb is NOT a standard degree achievement: its variable telicity
    does not reduce to scale boundedness alone. -/
def crack : Verb := .mkRegular {
  form := "crack"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  scaleDimension := some .cracking
  causative := some .make
  levinClasses := {LevinClass.break_, .soundEmission} }

/-- "dent" — Levin 21.2 Carve verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale, compatible with *more dented*, *completely
    dented*, *badly dented*. -/
def dent : Verb := .mkRegular {
  form := "dent"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  scaleDimension := some .denting
  causative := some .make
  levinClasses := {LevinClass.carve} }

/-- "scratch" — Levin 21.1 Cut verbs, a physical disturbance CoS verb for
    [tham-2025]: closed scale, compatible with *more scratched*, *completely
    scratched*, *badly scratched*. Levin also lists it among the wipe verbs
    (§10.4.1) and the swat verbs (§18.2) on its manner readings. -/
def scratch : Verb := .mkRegular {
  form := "scratch"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  scaleDimension := some .scratching
  causative := some .make
  levinClasses := {LevinClass.cut, .hurt, .rummage, .scribble, .swat, .wipeManner} }

/-- "shatter" — Levin 45.1 Break verbs. NOT a physical disturbance verb.
    Punctual, non-gradable: *shatter in two minutes* (after, not duration),
    #*shatter for two minutes*, ??*more shattered* ([tham-2025] (12)). -/
def shatter : Verb := .mkRegular {
  form := "shatter"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  causative := some .make
  levinClasses := {LevinClass.break_} }

/-- "burn" — destruction or transformation by fire or heat; Levin 45.4 other change-of-state
    verbs. -/
def burn : Verb := .mkRegular {
  form := "burn"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  causative := some .make
  root := { content := {
    force := {.moderate, .high}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.totalDestruction, .deformation}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.entitySpecificChangeOfState, .entitySpecificModeOfBeing, .hurt,
    .lightEmission, .otherChangeOfState, .tingle} }

/-- "destroy" — Levin 44 destroy verbs. -/
def destroy : Verb := .mkRegular {
  form := "destroy"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.destroy} }

/-- "melt" — change of consistency by heat; Levin 45.4 other change-of-state verbs. A base
    transitive that takes a double-object benefactive ("melt me some ice cream") and an
    indefinite implicit object ("the ice cream melted" / "we're melting"). -/
def melt : Verb := .mkRegular {
  form := "melt"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef), ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  causative := some .make
  root := { content := {
    force := {.low, .moderate}
    patientRobustness := {.moderate, .robust}
    resultGeometry := {.deformation}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.knead, .otherChangeOfState} }

/-! ### Further change-of-state verbs

The causative verbs Martin, Rose and Nichols survey that have no entry elsewhere in this
file. -/

/-- "activate" — sets a device or process in operation; not listed by Levin. -/
def activate : Verb := .mkRegular {
  form := "activate"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
 }

/-- "affect" — Levin 31.1 amuse verbs. -/
def affect : Verb := .mkRegular {
  form := "affect"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.amuse} }

/-- "change" — transformation; Levin 26.6 turn verbs. -/
def change : Verb := .mkRegular {
  form := "change"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.into),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial) (some Adpositions.from_),
      .adpositional (some .spatial) (some Adpositions.into)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.dress, .exchange, .otherChangeOfState, .turn} }

/-- "damage" — partial destruction; not listed by Levin. -/
def damage : Verb := .mkRegular {
  form := "damage"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "eliminate" — removal; Levin 42.1 murder verbs. -/
def eliminate : Verb := .mkRegular {
  form := "eliminate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.murder, .remove} }

/-- "hurt" — Levin 40.8.3 hurt verbs. -/
def hurt : Verb where
  form := "hurt"
  form3sg := "hurts"
  formPast := "hurt"
  formPastPart := "hurt"
  formPresPart := "hurting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .hurt, .marvel, .pain}

/-- "restore" — Levin 13.2 contribute verbs. -/
def restore : Verb := .mkRegular {
  form := "restore"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute} }

/-- "trigger" — sets a process off; not listed by Levin. -/
def trigger : Verb := .mkRegular {
  form := "trigger"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement }

/-- "bury" — covering with earth. Levin's concealment class (§16) does not list *bury*. -/
def bury : Verb := .mkRegular {
  form := "bury"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "drop" — Levin 45.6 calibratable change-of-state verbs. -/
def drop : Verb := .mkRegular {
  form := "drop"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.calibratableChangeOfState, .meander, .putDirection, .roll} }

/-- "lift" — Levin 9.4 verbs of putting with a specified direction. -/
def lift : Verb := .mkRegular {
  form := "lift"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.putDirection, .steal} }

/-- "lock" — securing with a lock; Levin lists *lock* only among the tape verbs (§22.4). -/
def lock : Verb := .mkRegular {
  form := "lock"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.tape} }


/-- "shut" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def shut : Verb where
  form := "shut"
  form3sg := "shuts"
  formPast := "shut"
  formPastPart := "shut"
  formPresPart := "shutting"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.otherChangeOfState}

/-- "spread" — Levin 9.7 spray/load verbs. -/
def spread : Verb where
  form := "spread"
  form3sg := "spreads"
  formPast := "spread"
  formPastPart := "spread"
  formPresPart := "spreading"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative, ArgumentFrame.pp (some Adpositions.at_),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.appear, .entitySpecificModeOfBeing, .sprayLoad}

/-- "stretch" — Levin 45.4 other change-of-state verbs. -/
def stretch : Verb := .mkRegular {
  form := "stretch"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.crane, .meander, .otherChangeOfState} }

/-- "switch" — Levin's change-of-state lists do not include *switch*. -/
def switch : Verb := .mkRegular {
  form := "switch"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
 }

/-- "close" — Levin 45.4 other change-of-state verbs, zero-related to the adjective, and
    40.3.2 crane verbs (*close one's eyes*). -/
def close : Verb := .mkRegular {
  form := "close"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.crane, .otherChangeOfState} }

/-- "dry" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def dry : Verb := .mkRegular {
  form := "dry"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  scaleDimension := some .wetness
  scalePolarity := .negative
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "enhance" — improvement in quality; not listed by Levin. -/
def enhance : Verb := .mkRegular {
  form := "enhance"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment }

/-- "extend" — Levin 47.1 exist verbs, 13.2 contribute verbs and 13.3 verbs of future
    having. -/
def extend : Verb := .mkRegular {
  form := "extend"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute, .exist, .futureHaving} }

/-- "lower" — Levin 9.4 verbs of putting with a specified direction. -/
def lower : Verb := .mkRegular {
  form := "lower"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.putDirection} }

/-- "slow" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def slow : Verb := .mkRegular {
  form := "slow"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .activity
  scaleDimension := some .speed
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "turn" — Levin 26.6 turn verbs (*turn the prince into a frog*). -/
def turn : Verb := .mkRegular {
  form := "turn"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.into)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.turn} }

/-- "wake up" — the particle verb of awakening; Levin lists *waken* but not *wake*. -/
def wakeUp : Verb where
  form := "wake up"
  form3sg := "wakes up"
  formPast := "woke up"
  formPastPart := "woken up"
  formPresPart := "waking up"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .achievement

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

/-! ### Communication -/

/-- "say" — communication verb, not factive -/
def say : Verb where
  form := "say"
  form3sg := "says"
  formPast := "said"
  formPastPart := "said"
  formPresPart := "saying"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClasses := {LevinClass.say}

/-- "tell" — communication verb with recipient.
    Also ditransitive ("tell me a story"). Implicit second obj is definite
    ([bruening-2021]: recoverable). Implicit goal (PP) is indefinite. -/
def tell : Verb where
  form := "tell"
  form3sg := "tells"
  formPast := "told"
  formPastPart := "told"
  formPresPart := "telling"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.np_np,
    ⟨some .nominal, [.implicit (some .def), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClasses := {LevinClass.tell, .transferOfMessage}

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : Verb := .mkRegular {
  form := "claim"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClasses := {LevinClass.say} }

/-! ### Clause-Embedding Predicates -/

/-! The 20 clause-embedding predicates of [degen-tonhauser-2022].
    Predicates already defined above: know, discover, see, think, say, hear.
    "be annoyed" and "be right" are copular constructions, not simple verbs. -/

/-- "reveal" — factive communication verb ([degen-tonhauser-2022]: canonically factive) -/
def reveal : Verb := .mkRegular {
  form := "reveal"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  attitude := some (.doxastic .veridical)
  factivity := some .full
  levinClasses := {LevinClass.characterize, .say} }

/-- "acknowledge" — optionally factive communication verb
    Levin lists *acknowledge* only among the appoint verbs (§29.1), a different frame. -/
def acknowledge : Verb := .mkRegular {
  form := "acknowledge"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint} }


/-- "admit" — optionally factive communication verb
    Levin lists *admit* among the conjecture verbs (§29.5). -/
def admit : Verb where
  form := "admit"
  form3sg := "admits"
  formPast := "admitted"
  formPastPart := "admitted"
  formPresPart := "admitting"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.conjecture}

/-- "announce" — communication verb -/
def announce : Verb := .mkRegular {
  form := "announce"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.say} }

/-- "confess" — optionally factive communication verb -/
def confess : Verb := .mkRegular {
  form := "confess"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare, .say} }

/-- "inform" — optionally factive communication verb with recipient -/
def inform : Verb := .mkRegular {
  form := "inform"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement }

/-- "suggest" — non-factive communication verb -/
def suggest : Verb := .mkRegular {
  form := "suggest"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.reflexiveAppearance, .say} }

/-- "pretend" — anti-veridical attitude verb -/
def pretend : Verb := .mkRegular {
  form := "pretend"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  opaqueContext := true }

/-- "confirm" — evidential verb -/
def confirm : Verb := .mkRegular {
  form := "confirm"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize} }

/-- "demonstrate" — evidential verb -/
def demonstrate : Verb := .mkRegular {
  form := "demonstrate"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage} }

/-- "establish" — evidential verb -/
def establish : Verb := .mkRegular {
  form := "establish"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize} }

/-- "prove" — evidential verb -/
def prove : Verb := .mkRegular {
  form := "prove"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare} }

/-! ### Manner of Speaking (Levin 37.3) -/

/-! Manner-of-speaking (MoS) verbs specify *how* something is said.
    [storment-2026] shows these divide into two classes:
    - **QI-permitting** (unaccusative): whisper, murmur, mumble, mutter, shout,
      cry, scream, shriek, yell, groan, grumble, hiss, sigh, whimper, snap
    - **Non-QI** (unergative): speak, talk -/

/-- "whisper" — Levin 37.3 Manner of Speaking verbs. -/
def whisper : Verb := .mkRegular {
  form := "whisper"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "murmur" — Levin 37.3 Manner of Speaking verbs. -/
def murmur : Verb := .mkRegular {
  form := "murmur"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission} }

/-- "shout" — Levin 37.3 Manner of Speaking verbs. -/
def shout : Verb := .mkRegular {
  form := "shout"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "cry" — Levin 37.3 Manner of Speaking verbs. -/
def cry : Verb := .mkRegular {
  form := "cry"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .mannerOfSpeaking, .marvel, .nonverbalExpression,
    .soundEmission} }

/-- "scream" — Levin 37.3 Manner of Speaking verbs. -/
def scream : Verb := .mkRegular {
  form := "scream"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking, .soundEmission} }

/-- "mumble" — Levin 37.3 Manner of Speaking verbs. -/
def mumble : Verb := .mkRegular {
  form := "mumble"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "mutter" — Levin 37.3 Manner of Speaking verbs. -/
def mutter : Verb := .mkRegular {
  form := "mutter"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking} }

/-- "shriek" — Levin 37.3 Manner of Speaking verbs. -/
def shriek : Verb := .mkRegular {
  form := "shriek"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission} }

/-- "yell" — Levin 37.3 Manner of Speaking verbs. -/
def yell : Verb := .mkRegular {
  form := "yell"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking} }

/-- "groan" — Levin 37.3 Manner of Speaking verbs. -/
def groan : Verb := .mkRegular {
  form := "groan"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .nonverbalExpression, .soundEmission} }

/-- "grumble" — Levin 37.3 Manner of Speaking verbs. -/
def grumble : Verb := .mkRegular {
  form := "grumble"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.complain, .mannerOfSpeaking} }

/-- "hiss" — Levin 37.3 Manner of Speaking verbs. -/
def hiss : Verb := .mkRegular {
  form := "hiss"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking, .soundEmission} }

/-- "sigh" — Levin 40.2 Nonverbal Expression verbs. -/
def sigh : Verb := .mkRegular {
  form := "sigh"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonverbalExpression} }

/-- "whimper" — Levin 37.3 Manner of Speaking verbs. -/
def whimper : Verb := .mkRegular {
  form := "whimper"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking} }

/-- "snap" — Levin 37.3 Manner of Speaking verbs. -/
def snap : Verb := .mkRegular {
  form := "snap"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .break_, .crane, .mannerOfSpeaking, .soundEmission} }

/-- "speak" — agentive communication verb, blocks quotative inversion (unergative)
    Levin 37.5 Talk verbs. -/
def speak : Verb where
  form := "speak"
  form3sg := "speaks"
  formPast := "spoke"
  formPastPart := "spoken"
  formPresPart := "speaking"
  speechActVerb := true
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.talk}

/-- "talk" — agentive communication verb, blocks quotative inversion (unergative)
    Levin 37.5 Talk verbs. -/
def talk : Verb := .mkRegular {
  form := "talk"
  speechActVerb := true
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.talk} }

/-! ### Question-Embedding -/

/-- "wonder" — embeds questions only -/
def wonder : Verb := .mkRegular {
  form := "wonder"
  frames := [ArgumentFrame.question]
  vendlerClass := some .state
  opaqueContext := true
  levinClasses := {LevinClass.marvel} }

/-- "ask" — embeds questions -/
def ask : Verb := .mkRegular {
  form := "ask"
  speechActVerb := true
  frames := [ArgumentFrame.question]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage} }

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : Verb := .mkRegular {
  form := "investigate"
  frames := [ArgumentFrame.question, ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.investigate, .sight} }

/-- "depend_on" — rogative, embeds interrogatives only ([dayal-2025]: a rogative predicate) -/
def depend_on : Verb where
  form := "depend on"
  form3sg := "depends on"
  formPast := "depended on"
  formPastPart := "depended on"
  formPresPart := "depending on"
  frames := [ArgumentFrame.question]
  vendlerClass := some .state

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : Verb := .mkRegular {
  form := "remember"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .semi
  senseTag := .rogative
  levinClasses := {LevinClass.characterize} }

/-- "forget" in factive/question-embedding sense. -/
def forget_rog : Verb where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .veridical)
  factivity := some .full
  senseTag := .rogative

/-! ### Prerequisite implicatives -/

/-! Implicatives whose complement is entailed through a prerequisite the verb names,
[nadathur-2023-implicatives]'s causal analysis of *manage*, *dare* and their kin; the
occasion verbs of [solstad-bott-2024] (*thank*, *criticize*, *congratulate*) presuppose an
occasioning eventuality in a parallel way the authors draw and then set apart. -/

/-- "dare" — a positive implicative whose prerequisite presupposition is courage. "Ana dared
    to enter the cave" entails "Ana entered the cave" and presupposes that a daring action was
    required for the complement to be realized ([nadathur-2023-implicatives] §5.2, ex. 3–4,
    26). -/
def dare : Verb := .mkRegular {
  form := "dare"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "bother" — a positive implicative whose prerequisite presupposition is engagement. "He
    bothered to answer" entails "He answered" and presupposes that apathy had to be overcome
    ([nadathur-2023-implicatives] §2, ex. 10, 28). -/
def bother : Verb := .mkRegular {
  form := "bother"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive
  levinClasses := {LevinClass.amuse, .pain} }

/-- "hesitate" — polarity-reversing one-way implicative.
    "Amira hesitated to drink a beer" ↛ "Amira did not drink a beer."
    "Amira did not hesitate to drink a beer" → "Amira drank a beer."
    The paper does not explicitly name the prerequisite for *hesitate*;
    it is treated as a polarity-reversing analog of *dare*
    ([nadathur-2023-implicatives] §6.4, ex. 45–47). -/
def hesitate : Verb := .mkRegular {
  form := "hesitate"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  implicative := some .negative
  levinClasses := {LevinClass.linger} }

/-- "venture" — positive implicative, among [karttunen-1971]'s implicative
    predicates: venturing to speak entails speaking. -/
def venture : Verb := .mkRegular {
  form := "venture"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "condescend" — positive implicative, among [karttunen-1971]'s implicative
    predicates: condescending to help entails helping. -/
def condescend : Verb := .mkRegular {
  form := "condescend"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "happen" — raising verb, positive implicative, among [karttunen-1971]'s
    implicative predicates: happening to see Mary entails seeing her.
    Raising: "It happened to rain" — no theta role for matrix subject. -/
def happen : Verb := .mkRegular {
  form := "happen"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .raising }]
  passivizable := false
  implicative := some .positive
  levinClasses := {LevinClass.occurrence} }

/-! ### Agent-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.2 (admire). Subject = experiencer, object = stimulus.
    NP1 (subject) IC bias. -/

/-- "enjoy" — AgExp verb (experiencer-subject) -/
def enjoy : Verb := .mkRegular {
  form := "enjoy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "like" — AgExp verb (experiencer-subject) -/
def like : Verb := .mkRegular {
  form := "like"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "love" — AgExp verb (experiencer-subject) -/
def love : Verb := .mkRegular {
  form := "love"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : Verb := .mkRegular {
  form := "hate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : Verb := .mkRegular {
  form := "admire"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "envy" — AgExp verb (experiencer-subject).
    DOC-only ditransitive ("He envies me the car"). Implicit goal is
    definite (familiar). Implicit second obj is indefinite. -/
def envy : Verb := .mkRegular {
  form := "envy"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : Verb := .mkRegular {
  form := "respect"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-- "value" — AgExp verb (experiencer-subject) -/
def value : Verb := .mkRegular {
  form := "value"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .characterize, .price} }

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : Verb := .mkRegular {
  form := "fear"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .marvel} }

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : Verb := .mkRegular {
  form := "dread"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.admire} }

/-! ### Stimulus-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def frighten : Verb := .mkRegular {
  form := "frighten"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "amuse" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def amuse : Verb := .mkRegular {
  form := "amuse"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "fascinate" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def fascinate : Verb := .mkRegular {
  form := "fascinate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "irritate" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def irritate : Verb := .mkRegular {
  form := "irritate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "annoy" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def annoy : Verb := .mkRegular {
  form := "annoy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "bore" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def bore : Verb := .mkRegular {
  form := "bore"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse, .carve, .rummage} }

/-- "charm" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def charm : Verb := .mkRegular {
  form := "charm"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "impress" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def impress : Verb := .mkRegular {
  form := "impress"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "concern" — stative Class II psych verb ([kim-2024] UPH, internal cause) -/
def concern : Verb := .mkRegular {
  form := "concern"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClasses := {LevinClass.amuse} }

/-- "interest" — stative Class II psych verb ([kim-2024] UPH, internal cause) -/
def interest : Verb := .mkRegular {
  form := "interest"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClasses := {LevinClass.amuse} }

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : Verb := .mkRegular {
  form := "surprise"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : Verb := .mkRegular {
  form := "scare"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : Verb := .mkRegular {
  form := "delight"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse, .marvel} }

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : Verb := .mkRegular {
  form := "embarrass"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : Verb := .mkRegular {
  form := "upset"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : Verb := .mkRegular {
  form := "disgust"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : Verb := .mkRegular {
  form := "shock"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : Verb := .mkRegular {
  form := "confuse"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amalgamate, .amuse} }

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : Verb := .mkRegular {
  form := "disappoint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "worry" (eventive) — Class II, external cause. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : Verb := .mkRegular {
  form := "worry"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClasses := {LevinClass.amuse} }

/-- "worry" (stative) — Class II, internal cause. "The situation worries John."
    [kim-2024] UPH: same theta grid as worry_eventive, different causal source. -/
def worry_stative : Verb := .mkRegular {
  form := "worry"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClasses := {LevinClass.amuse} }

/-- "please" — stative Class II ([kim-2024] UPH, internal cause).
    "The idea pleases John." Related to B&R Class III It. *piacere*. -/
def please_psych : Verb := .mkRegular {
  form := "please"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClasses := {LevinClass.amuse} }

/-- "trouble" — stative Class II ([kim-2024] UPH, internal cause).
    "The thought troubles John." -/
def trouble : Verb := .mkRegular {
  form := "trouble"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClasses := {LevinClass.amuse} }

/-- "puzzle" — stative Class II ([kim-2024] UPH, internal cause).
    "The problem puzzles John." -/
def puzzle : Verb := .mkRegular {
  form := "puzzle"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClasses := {LevinClass.amuse, .marvel} }

/-! ### Agent-patient verbs ([solstad-bott-2024]) -/

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : Verb := .mkRegular {
  form := "chase"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.chase} }

/-- "hit" — AgPat verb (Levin 18.1) -/
def hit : Verb where
  form := "hit"
  form3sg := "hits"
  formPast := "hit"
  formPastPart := "hit"
  formPresPart := "hitting"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.contiguousLocation, .hit, .nonAgentiveImpact, .throw}

/-- "push" — AgPat verb (Levin 12) -/
def push : Verb := .mkRegular {
  form := "push"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .funnel, .pushPull, .split} }

/-- "pull" — AgPat verb (Levin 12) -/
def pull : Verb := .mkRegular {
  form := "pull"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .get, .hurt, .pushPull, .split} }

/-- "shove" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def shove : Verb := .mkRegular {
  form := "shove"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carry, .pushPull, .split, .throw} }

/-- "tug" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def tug : Verb where
  form := "tug"
  form3sg := "tugs"
  formPast := "tugged"
  formPastPart := "tugged"
  formPresPart := "tugging"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carry, .pushPull, .split}

/-- "yank" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def yank : Verb := .mkRegular {
  form := "yank"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.pushPull, .split} }

/-- "jerk" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def jerk : Verb := .mkRegular {
  form := "jerk"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.pushPull} }

/-- "wrench" — verb of exerting force for [levin-2026] (31); not among the
    members of Levin's §12. -/
def wrench : Verb := .mkRegular {
  form := "wrench"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.remove} }


/-- "fling" — Levin 17.1 Throw verbs; a verb of exerting force for
    [levin-2026] (31). Irregular past. -/
def fling : Verb where
  form := "fling"
  form3sg := "flings"
  formPast := "flung"
  formPastPart := "flung"
  formPresPart := "flinging"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.throw}

/-- "slam" — Levin 17.1 Throw verbs; a hitting verb for [levin-2026] (32a).
    Irregular doubling. -/
def slam : Verb where
  form := "slam"
  form3sg := "slams"
  formPast := "slammed"
  formPastPart := "slammed"
  formPresPart := "slamming"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonAgentiveImpact, .throw}

/-- "punch" — Levin 18.2 Swat verbs; a hitting verb for [levin-2026] (32a). -/
def punch : Verb := .mkRegular {
  form := "punch"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.carve, .swat} }

/-- "smack" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def smack : Verb := .mkRegular {
  form := "smack"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.crane, .hit} }

/-- "thump" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def thump : Verb := .mkRegular {
  form := "thump"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.hit, .soundEmission} }

/-- "bang" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def bang : Verb := .mkRegular {
  form := "bang"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.funnel, .hit, .nonAgentiveImpact, .soundEmission} }

/-- "thrash" — Levin 18.3 Spank verbs; a hitting verb for [levin-2026] (32a). -/
def thrash : Verb := .mkRegular {
  form := "thrash"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.spank} }

/-- "hammer" — Levin 18.1 Hit verbs. -/
def hammer : Verb := .mkRegular {
  form := "hammer"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.build, .funnel, .hit} }

/-- "scrape" — verb of surface contact, wiping (Levin 10.4,
    [levin-2026] (32b)). In intr-push-open, enters through
    surface-contact sense, not removing sense. -/
def scrape : Verb := .mkRegular {
  form := "scrape"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.objectDrop (some .indef),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.cut, .funnel, .wipeManner} }

/-- "wipe" — Levin 10.4 Wipe verbs, manner subclass. -/
def wipe : Verb := .mkRegular {
  form := "wipe"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.objectDrop (some .indef),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.funnel, .wipeManner} }

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : Verb where
  form := "carry"
  form3sg := "carries"
  formPast := "carried"
  formPastPart := "carried"
  formPresPart := "carrying"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .cost, .fit}

/-- "drag" — AgPat verb (Levin 11.4/12) -/
def drag : Verb where
  form := "drag"
  form3sg := "drags"
  formPast := "dragged"
  formPastPart := "dragged"
  formPresPart := "dragging"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.carry, .search}

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : Verb := .mkRegular {
  form := "call"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .dub, .get, .mannerOfSpeaking} }

/-! ### Putting (§ 9) -/

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : Verb := .mkRegular {
  form := "place"
  frames := [ArgumentFrame.np_pp]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.put} }

/-- "water" — Levin 9.9 Butter verbs (denominal putting). -/
def water : Verb := .mkRegular {
  form := "water"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClasses := {LevinClass.butter} }

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : Verb := .mkRegular {
  form := "pour"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.pour, .prepare, .substanceEmission, .weather} }

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : Verb := .mkRegular {
  form := "spray"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative, ArgumentFrame.pp (some Adpositions.at_),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.sprayLoad} }

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : Verb := .mkRegular {
  form := "load"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative, ArgumentFrame.pp (some Adpositions.at_),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.sprayLoad} }

/-! ### Removing (§ 10) -/

/-- "remove" — Levin 10.1 Remove verbs. -/
def remove : Verb := .mkRegular {
  form := "remove"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.banish, .remove} }

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : Verb := .mkRegular {
  form := "clean"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .cleanliness
  incrementality := some .strict
  levinClasses := {LevinClass.clear, .otherChangeOfState, .prepare} }

/-- "steal" — Levin 10.5 Steal verbs. -/
def steal : Verb where
  form := "steal"
  form3sg := "steals"
  formPast := "stole"
  formPastPart := "stolen"
  formPresPart := "stealing"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.appear, .get, .steal}

/-! ### Sending and Carrying (§ 11) -/

/-- "send" — Levin 11.1 Send verbs. Alternates DOC/PP.
    Goal does not entail possession (prospective). Neither object implicit alone. -/
def send : Verb where
  form := "send"
  form3sg := "sends"
  formPast := "sent"
  formPastPart := "sent"
  formPresPart := "sending"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send}

/-- "drive" — Levin 11.5 Drive verbs (vehicle-mediated motion). -/
def drive : Verb where
  form := "drive"
  form3sg := "drives"
  formPast := "drove"
  formPastPart := "driven"
  formPresPart := "driving"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.drive, .nonVehicleName}

/-! ### Change of Possession (§ 13) -/

/-- "donate" — Levin 13.2 Contribute verbs. -/
def donate : Verb := .mkRegular {
  form := "donate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute} }

/-- "obtain" — Levin 13.5.2 Obtain verbs. -/
def obtain : Verb := .mkRegular {
  form := "obtain"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.for_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.obtain} }

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : Verb := .mkRegular {
  form := "trade"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.exchange, .give} }

/-! ### Learn, Hold, Conceal (§ 14–16) -/

/-- "learn" — Levin 14 Learn verbs. -/
def learn : Verb := .mkRegular {
  form := "learn"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.learn} }

/-- "hold" — Levin 15.1 Hold verbs. Stative. -/
def hold : Verb where
  form := "hold"
  form3sg := "holds"
  formPast := "held"
  formPastPart := "held"
  formPresPart := "holding"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on)]
  vendlerClass := some .state
  levinClasses := {LevinClass.conjecture, .fit, .hold}

/-- "hide" — Levin 16 Conceal verbs. -/
def hide : Verb where
  form := "hide"
  form3sg := "hides"
  formPast := "hid"
  formPastPart := "hidden"
  formPresPart := "hiding"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conceal}

/-! ### Throwing (§ 17) -/

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. Alternates DOC/PP.
    Implicit DO in PP frame only (definite). -/
def throw : Verb where
  form := "throw"
  form3sg := "throws"
  formPast := "threw"
  formPastPart := "thrown"
  formPresPart := "throwing"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np,
    ⟨some .nominal, [.implicit (some .def), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amuse, .throw}

/-! ### Contact (§ 19–20) -/

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : Verb := .mkRegular {
  form := "poke"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.poke, .rummage} }

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : Verb := .mkRegular {
  form := "touch"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on),
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amuse, .contiguousLocation, .touch} }

/-! ### Cutting (§ 21) -/

/-- "cut" — Levin 21.1 Cut verbs. Incremental by length of cut.
    [majid-boster-bowerman-2008]: Dimension 1 high predictability —
    sharp instrument on yielding object → predictable locus of separation. -/
def cut : Verb where
  form := "cut"
  form3sg := "cuts"
  formPast := "cut"
  formPastPart := "cut"
  formPresPart := "cutting"
  frames := [ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    resultGeometry := {.surfaceBreach}
    instrument := {.sharpBlade}
  } }
  levinClasses := {LevinClass.amuse, .braid, .build, .cut, .hurt, .meander, .split}

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : Verb where
  form := "chop"
  form3sg := "chops"
  formPast := "chopped"
  formPastPart := "chopped"
  formPresPart := "chopping"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.carve}

/-! ### Combining and Separating (§ 22–23) -/

/-- "mix" — Levin 22.1 Mix verbs. Incremental by proportion combined. -/
def mix : Verb := .mkRegular {
  form := "mix"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.correspond, .mix, .prepare} }

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : Verb := .mkRegular {
  form := "separate"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.remove, .separate} }

/-! ### Coloring and Image Creation (§ 24–25) -/

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : Verb := .mkRegular {
  form := "paint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.characterize, .color, .imageImpression, .performance, .scribble} }

/-- "draw" — Levin 25 Image Creation verbs. Incremental by extent. -/
def draw : Verb where
  form := "draw"
  form3sg := "draws"
  formPast := "drew"
  formPastPart := "drawn"
  formPresPart := "drawing"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.performance, .pushPull, .remove, .scribble, .split}

/-! ### Creation and Transformation (§ 26) -/

/-- "create" — Levin 26.4 Create verbs. -/
def create : Verb := .mkRegular {
  form := "create"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.create, .engender} }

/-- "weave" — Levin 26.1 Build verbs. -/
def weave : Verb where
  form := "weave"
  form3sg := "weaves"
  formPast := "wove"
  formPastPart := "woven"
  formPresPart := "weaving"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef),
    ArgumentFrame.np_pp (some Adpositions.for_), ArgumentFrame.np_np,
    ArgumentFrame.np_pp (some Adpositions.outOf), ArgumentFrame.np_pp (some Adpositions.into)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.build, .meander}

/-- "grow" — Levin 26.2 Grow verbs. Incremental by size. -/
def grow : Verb where
  form := "grow"
  form3sg := "grows"
  formPast := "grew"
  formPastPart := "grown"
  formPresPart := "growing"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.outOf), ArgumentFrame.np_pp (some Adpositions.into)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.appear, .build, .calibratableChangeOfState,
    .entitySpecificModeOfBeing, .grow, .otherChangeOfState}

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : Verb := .mkRegular {
  form := "perform"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef),
    ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np,
    ArgumentFrame.np_pp (some Adpositions.for_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.performance} }

/-! ### Predicative Complements (§ 29) -/

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : Verb := .mkRegular {
  form := "appoint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint} }

/-! ### Perception (§ 30) -/

/-- "hear" — Levin 30.1 See verbs. Stative perception. Also embeds
    finite clauses (optionally factive per [degen-tonhauser-2022]). -/
def hear : Verb where
  form := "hear"
  form3sg := "hears"
  formPast := "heard"
  formPastPart := "heard"
  formPresPart := "hearing"
  frames := [ArgumentFrame.np, ArgumentFrame.finiteClause]
  vendlerClass := some .state
  levinClasses := {LevinClass.see}

/-! ### Judgment and Assessment (§ 33–34) -/

/-- "blame" — a judgment verb by sense, absent from Levin's §33 member lists
    and named only for the blame alternation (§2.10). -/
def blame : Verb := .mkRegular {
  form := "blame"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  incrementality := some .cumulative
 }

/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : Verb := .mkRegular {
  form := "evaluate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.assessment} }

/-! ### Social Interaction (§ 36) -/

/-- "marry" — Levin 36 Social Interaction verbs. -/
def marry : Verb where
  form := "marry"
  form3sg := "marries"
  formPast := "married"
  formPastPart := "married"
  formPresPart := "marrying"
  frames := [ArgumentFrame.np, ArgumentFrame.objectDrop (some .reciprocal)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amalgamate, .marry}

/-! ### Animal Sounds (§ 38) -/

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : Verb := .mkRegular {
  form := "bark"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .hurt, .mannerOfSpeaking, .pit} }

/-! ### Body (§ 40–41) -/

/-- "breathe" — Levin 40.1 Body Process verbs. -/
def breathe : Verb := .mkRegular {
  form := "breathe"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .entitySpecificModeOfBeing} }

/-- "laugh" — Levin 40.2 Nonverbal Expression verbs. -/
def laugh : Verb := .mkRegular {
  form := "laugh"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonverbalExpression} }

/-- "cough" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary event, no result state ([smith-1997] §2.4.3). -/
def cough : Verb := .mkRegular {
  form := "cough"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.breathe, .nonverbalExpression} }

/-- "hiccup" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary body event ([smith-1997] §2.4.3). -/
def hiccup : Verb := .mkRegular {
  form := "hiccup"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hiccup} }

/-- "blink" — a semelfactive, a single instantaneous eye movement by [smith-1997]'s
    characterization of the class. Levin lists *blink (eye)* among the wink verbs (§40.3.1)
    and *blink* among the light-emission verbs (§43.1); this entry is the eye movement, a
    class the library does not name. -/
def blink : Verb where
  form := "blink"
  form3sg := "blinks"
  formPast := "blinked"
  formPastPart := "blinked"
  formPresPart := "blinking"
  frames := [ArgumentFrame.intransitive,
    ArgumentFrame.np, ArgumentFrame.objectDrop (some .bodyPart)]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.wink}
  levinExcluded := {LevinClass.lightEmission}

/-- "knock" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single percussive contact event, [smith-1997]'s standard
    example of the class. -/
def knock : Verb := .mkRegular {
  form := "knock"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hit, .nonAgentiveImpact, .soundEmission, .split, .throw} }

/-- "tap" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single light percussive contact event ([smith-1997] §2.4.3). -/
def tap : Verb := .mkRegular {
  form := "tap"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.pp (some Adpositions.at_),
    ArgumentFrame.np_pp (some Adpositions.on), ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hit, .investigate, .throw} }

/-- "flash" — Levin 43.1 Light Emission verbs.
    Semelfactive: single instantaneous light event, by [smith-1997]'s
    characterization of the class. -/
def flash : Verb := .mkRegular {
  form := "flash"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative,
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.crane, .lightEmission} }

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : Verb := .mkRegular {
  form := "flinch"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.flinch} }

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : Verb := .mkRegular {
  form := "dress"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.objectDrop (some .reflexive)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.dress, .dressingWell} }

/-! ### Killing (§ 42) -/

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : Verb := .mkRegular {
  form := "drown"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClasses := {LevinClass.poison, .suffocate} }

/-! ### Emission (§ 43) -/

/-- "glow" — Levin 43.1 Light Emission verbs. -/
def glow : Verb := .mkRegular {
  form := "glow"
  frames := [ArgumentFrame.unaccusative, ArgumentFrame.np,
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.lightEmission} }

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : Verb := .mkRegular {
  form := "buzz"
  frames := [ArgumentFrame.unaccusative, ArgumentFrame.np,
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .soundEmission} }

/-- "rumble" — Levin 43.2 Sound Emission verbs. -/
def rumble : Verb := .mkRegular {
  form := "rumble"
  frames := [ArgumentFrame.unaccusative, ArgumentFrame.np,
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission} }

/-- "bleed" — Levin 43.4 Substance Emission verbs. -/
def bleed : Verb where
  form := "bleed"
  form3sg := "bleeds"
  formPast := "bled"
  formPastPart := "bled"
  formPresPart := "bleeding"
  frames := [ArgumentFrame.unaccusative, ArgumentFrame.np,
    ArgumentFrame.pp (some Adpositions.from_),
    ⟨some .nominal, [.nominal, .adpositional (some .spatial)]⟩,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .cheat, .substanceEmission}

/-! ### Change of State (§ 45) -/

/-- "freeze" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def freeze : Verb where
  form := "freeze"
  form3sg := "freezes"
  formPast := "froze"
  formPastPart := "frozen"
  formPresPart := "freezing"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClasses := {LevinClass.knead, .otherChangeOfState, .weather}

/-- "heat" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def heat : Verb := .mkRegular {
  form := "heat"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClasses := {LevinClass.cooking, .otherChangeOfState} }

/-- "bend" — Levin 45.2 Bend verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (straight → bent, has maximal endpoint). -/
def bend : Verb where
  form := "bend"
  form3sg := "bends"
  formPast := "bent"
  formPastPart := "bent"
  formPresPart := "bending"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .curvature
  causative := some .make
  levinClasses := {LevinClass.assumePosition, .bend, .knead, .spatialConfiguration}

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : Verb := .mkRegular {
  form := "boil"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .boiling
  causative := some .make
  levinClasses := {LevinClass.cooking} }

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : Verb := .mkRegular {
  form := "rust"
  frames := [ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  scaleDimension := some .corrosion
  levinClasses := {LevinClass.entitySpecificChangeOfState, .entitySpecificModeOfBeing} }

/-- "increase" — Levin 45.6 Calibratable CoS verbs (degree achievements).
    Degree achievement: open scale (no maximum quantity). -/
def increase : Verb := .mkRegular {
  form := "increase"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative]
  vendlerClass := some .activity
  scaleDimension := some .quantity
  levinClasses := {LevinClass.calibratableChangeOfState, .otherChangeOfState} }

/-! ### Degree achievement verb pairs ([kennedy-2007]) -/

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : Verb := .mkRegular {
  form := "straighten"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .straightness
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "flatten" — Closed-scale degree achievement (base adj: flat).
    Accomplishment: "flattened the dough in 2 minutes." -/
def flatten : Verb := .mkRegular {
  form := "flatten"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .flatness
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "open" — Closed-scale degree achievement (base adj: open, closed scale).
    Accomplishment: "opened the door in 3 seconds." -/
def open_ : Verb := .mkRegular {
  form := "open"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .accomplishment
  scaleDimension := some .openness
  levinClasses := {LevinClass.appear, .crane, .otherChangeOfState, .spatialConfiguration} }

/-- "lengthen" — Open-scale degree achievement (base adj: long, open scale).
    Activity: "lengthened the rope for hours." -/
def lengthen : Verb := .mkRegular {
  form := "lengthen"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .length
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "widen" — Open-scale degree achievement (base adj: wide, open scale).
    Activity: "widened the road for months." -/
def widen : Verb := .mkRegular {
  form := "widen"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .width
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "cool" — Open-scale degree achievement (base adj: cool, open scale).
    Activity: "cooled for an hour." -/
def cool : Verb := .mkRegular {
  form := "cool"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .temperature
  levinClasses := {LevinClass.otherChangeOfState} }

/-- "warm" — Open-scale degree achievement (base adj: warm, open scale).
    Activity: "warmed for an hour." -/
def warm : Verb := .mkRegular {
  form := "warm"
  frames := [ArgumentFrame.np, ArgumentFrame.unaccusative,
    ArgumentFrame.np_pp (some Adpositions.with_)]
  vendlerClass := some .activity
  scaleDimension := some .temperature
  levinClasses := {LevinClass.otherChangeOfState} }

/-! ### Existence, Appearance, Position (§ 47–50) -/

/-- "exist" — Levin 47.1 Exist verbs. Pure state. -/
def exist : Verb := .mkRegular {
  form := "exist"
  frames := [ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.exist, .gorge} }

/-- "appear" — Levin 48.1 Appear verbs. Punctual emergence. -/
def appear : Verb := .mkRegular {
  form := "appear"
  frames := [ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appear} }

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : Verb := .mkRegular {
  form := "fidget"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.bodyInternalMotion} }

/-- "sit" — Levin 50 Assume Position verbs. Stative. -/
def sit : Verb where
  form := "sit"
  form3sg := "sits"
  formPast := "sat"
  formPastPart := "sat"
  formPresPart := "sitting"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.assumePosition, .putInSpatialConfiguration, .spatialConfiguration}

/-- "stand" — Levin 50 Assume Position verbs. Stative. -/
def stand : Verb where
  form := "stand"
  form3sg := "stands"
  formPast := "stood"
  formPastPart := "stood"
  formPresPart := "standing"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .assumePosition, .putInSpatialConfiguration,
    .spatialConfiguration}

/-! ### Motion (§ 51) -/

/-- "walk" — Levin 51.3 Manner of Motion verbs. -/
def walk : Verb := .mkRegular {
  form := "walk"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.run} }

/-- "swim" — Levin 51.3 Manner of Motion verbs. -/
def swim : Verb where
  form := "swim"
  form3sg := "swims"
  formPast := "swam"
  formPastPart := "swum"
  formPresPart := "swimming"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.run, .swarm, .tingle}

/-- "fly" — Levin 51.4 Vehicle Motion verbs. -/
def fly : Verb where
  form := "fly"
  form3sg := "flies"
  formPast := "flew"
  formPastPart := "flown"
  formPresPart := "flying"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.drive, .nonVehicleName, .run, .spatialConfiguration}

/-- "roll" — Levin 51.3.1 Roll verbs (manner of motion). -/
def roll : Verb := .mkRegular {
  form := "roll"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.build, .coil, .crane, .prepare, .roll, .run, .shake, .slide,
    .soundEmission, .split} }

/-- "float" — Levin 51.3.1 Roll verbs (manner of motion). -/
def float : Verb := .mkRegular {
  form := "float"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .roll, .run, .slide} }

/-! ### Avoid, Linger, Rush (§ 52–53) -/

/-- "avoid" — Levin 52 Avoid verbs. Stative. -/
def avoid : Verb := .mkRegular {
  form := "avoid"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClasses := {LevinClass.avoid} }

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : Verb := .mkRegular {
  form := "linger"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.exist, .linger} }

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : Verb := .mkRegular {
  form := "rush"
  frames := [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.unaccusative]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.run, .rush} }

/-! ### Weather (§ 57) -/

/-- "rain" — Levin 57 Weather verbs. Expletive subject. -/
def rain : Verb := .mkRegular {
  form := "rain"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.weather} }

/-! ### Ditransitive verbs and implicit arguments ([bruening-2021]) -/

/-! Ditransitive verbs classified by their implicit argument behavior,
    following [bruening-2021] Table (56). The classification is
    theory-neutral: it records surface optionality and interpretation
    without committing to a specific structural analysis. -/

-- DOC-only verbs (no PP frame alternant)

/-- "charge" — DOC-only. Implicit second obj indef, implicit goal def (addressee). -/
def charge : Verb := .mkRegular {
  form := "charge"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .equip, .run} }

/-- "cost" — DOC-only. Implicit second obj indef, implicit goal def. -/
def cost : Verb := .mkRegular {
  form := "cost"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .state
  levinClasses := {LevinClass.cost} }

/-- "fine" — DOC-only. Implicit second obj indef, implicit goal def. -/
def fine : Verb := .mkRegular {
  form := "fine"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .judgment} }

/-- "tip" — DOC-only. Implicit second obj indef, implicit goal def (unique). -/
def tip : Verb where
  form := "tip"
  form3sg := "tips"
  formPast := "tipped"
  formPastPart := "tipped"
  formPresPart := "tipping"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill, .throw}

/-- "pay" — DOC-only. Implicit second obj indef, implicit goal def. -/
def pay : Verb where
  form := "pay"
  form3sg := "pays"
  formPast := "paid"
  formPastPart := "paid"
  formPresPart := "paying"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "strike" — DOC-only. Implicit second obj indef, implicit goal def (familiar). -/
def strike_ : Verb where
  form := "strike"
  form3sg := "strikes"
  formPast := "struck"
  formPastPart := "struck"
  formPresPart := "striking"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .achievement
  senseTag := .default
  levinClasses := {LevinClass.amuse, .hit, .soundEmission}

/-- "forgive" — DOC-only. Implicit second obj def, implicit goal def (addressee). -/
def forgive : Verb where
  form := "forgive"
  form3sg := "forgives"
  formPast := "forgave"
  formPastPart := "forgiven"
  formPresPart := "forgiving"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .def)]⟩,
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.judgment}

/-- "spare" — DOC-only. Implicit second obj def, no implicit goal. -/
def spare : Verb := .mkRegular {
  form := "spare"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill} }

/-- "deny" — DOC-only. Implicit goal def; second object obligatory
    ([bruening-2021] Table 56 row 3 col 1, ex. (32d) p. 1032). -/
def deny : Verb where
  form := "deny"
  form3sg := "denies"
  formPast := "denied"
  formPastPart := "denied"
  formPresPart := "denying"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture}

/-- "permit" — DOC-only. Implicit goal def (addressee); second object
    obligatory ([bruening-2021] Table 56 row 3 col 1, ex. (32e) p. 1032). -/
def permit : Verb where
  form := "permit"
  form3sg := "permits"
  formPast := "permitted"
  formPastPart := "permitted"
  formPresPart := "permitting"
  frames := [ArgumentFrame.np_np, ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment

/-- "assign" — alternating (DOC + PP). Implicit goal definite; the second
    object is obligatory, Pesetsky's observation as [bruening-2021] report it. -/
def assign : Verb := .mkRegular {
  form := "assign"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_),
    ⟨some .nominal, [.implicit (some .def), .nominal]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving} }

-- DOC-only verbs with no implicit arguments

/-- "begrudge" — DOC-only. Neither object implicit. -/
def begrudge : Verb := .mkRegular {
  form := "begrudge"
  frames := [ArgumentFrame.np_np]
  vendlerClass := some .state }

/-- "bet" — DOC-only. Neither object implicit. -/
def bet : Verb where
  form := "bet"
  form3sg := "bets"
  formPast := "bet"
  formPastPart := "bet"
  formPresPart := "betting"
  frames := [ArgumentFrame.np_np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.bill}

-- Alternating verbs (both DOC and PP frame)

/-- "serve" — alternates DOC/PP. Implicit second obj indef (DOC).
    Implicit goal def (PP). -/
def serve : Verb := .mkRegular {
  form := "serve"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .indef), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.fit, .fulfilling, .give, .masquerade} }

/-- "teach" — alternates DOC/PP. Implicit goal indef (PP).
    When both implicit, both are indefinite. -/
def teach : Verb where
  form := "teach"
  form3sg := "teaches"
  formPast := "taught"
  formPastPart := "taught"
  formPresPart := "teaching"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .indef), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩]
  vendlerClass := some .activity
  levinClasses := {LevinClass.transferOfMessage}

/-- "feed" — alternates DOC/PP. Implicit second obj indef (DOC).
    No implicit goal. -/
def feed : Verb where
  form := "feed"
  form3sg := "feeds"
  formPast := "fed"
  formPastPart := "fed"
  formPresPart := "feeding"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩]
  vendlerClass := some .activity
  levinClasses := {LevinClass.feed, .fit, .give, .gorge}

/-- "show" — alternates DOC/PP. Implicit second obj def. No implicit goal. -/
def show_ : Verb where
  form := "show"
  form3sg := "shows"
  formPast := "showed"
  formPastPart := "shown"
  formPresPart := "showing"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .crane, .reflexiveAppearance, .transferOfMessage}

/-- "award" — alternates DOC/PP. Implicit goal def (PP). -/
def award : Verb := .mkRegular {
  form := "award"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_),
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.futureHaving} }

/-- "forward" — alternates DOC/PP. Implicit goal def (PP). -/
def forward_ : Verb := .mkRegular {
  form := "forward"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_),
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send} }

/-- "grant" — alternates DOC/PP. Implicit goal def (PP). -/
def grant : Verb := .mkRegular {
  form := "grant"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conjecture, .futureHaving} }

/-- "offer" — alternates DOC/PP. Implicit goal def (PP). -/
def offer : Verb := .mkRegular {
  form := "offer"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.characterize, .futureHaving, .reflexiveAppearance} }

/-- "reserve" — alternates DOC/PP. Implicit goal def (PP). -/
def reserve : Verb := .mkRegular {
  form := "reserve"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.for_),
    ⟨some .nominal, [.nominal, .implicit (some .def)]⟩]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get} }

/-- "pass" — alternates DOC/PP. Implicit DO def in PP frame only. -/
def pass : Verb := .mkRegular {
  form := "pass"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp,
    ⟨some .nominal, [.implicit (some .def), .adpositional]⟩,
    ⟨some .nominal, [.nominal, .implicit (some .indef)]⟩,
    ArgumentFrame.np_pp (some Adpositions.to_), ArgumentFrame.np_np]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give, .marry, .send, .throw} }

-- Alternating verbs with no implicit arguments

/-- "hand" — Levin 11.1 Send verbs; alternates DOC/PP, neither argument
    implicit. -/
def hand : Verb := .mkRegular {
  form := "hand"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send} }

/-- "lend" — alternates DOC/PP. Neither argument implicit. -/
def lend : Verb where
  form := "lend"
  form3sg := "lends"
  formPast := "lent"
  formPastPart := "lent"
  formPresPart := "lending"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp, ArgumentFrame.np_pp (some Adpositions.to_)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-! ### The inventory -/

/-- Every entry of the lexicon, in file order. -/
def verbs : List Verb :=
  [sleep, run, arrive, come, eat, kick, give, put,
   weigh, cover, measure, buy, meet, set_, clarify, sell,
   leave, see, know, regret, realize, discover, notice, stop,
   quit, start, begin_, continue_, keep, manage, fail, try_,
   persuade, promise, remember, forget, neglect, believe, think, want,
   intend, decide_, hope, pray, expect, wish, fear, dread,
   worry, seem, cause, make, let_, have_caus, get_caus, force,
   prevent, kill, break_, tear_, crack, dent, scratch, shatter,
   burn, destroy, melt, activate, affect, change, damage, eliminate,
   hurt, restore, trigger, bury, drop, lift, lock, shut,
   spread, stretch, switch, devour, drink, read, build, write,
   sweep, sweep_instr, say, tell, claim, reveal, acknowledge, admit,
   announce, confess, inform, suggest, pretend, confirm, demonstrate, establish,
   prove, whisper, murmur, shout, cry, scream, mumble, mutter,
   shriek, yell, groan, grumble, hiss, sigh, whimper, snap,
   speak, talk, wonder, ask, investigate, depend_on, remember_rog, forget_rog,
   dare, bother, hesitate, venture, condescend, happen, enjoy, like,
   love, hate, admire, envy, respect, value, fear_np, dread_np,
   frighten, amuse, fascinate, irritate, annoy, bore, charm, impress,
   concern, interest, surprise, scare, delight, embarrass, upset_psych, disgust,
   shock, confuse, disappoint, worry_eventive, worry_stative, please_psych, trouble, puzzle,
   chase, hit, push, pull, shove, tug, yank, jerk,
   wrench, fling, slam, punch, smack, thump, bang, thrash,
   hammer, scrape, wipe, carry, drag, call, place, water,
   pour, spray, load, remove, clean, steal, send, drive,
   donate, obtain, trade, learn, hold, hide, throw, poke,
   touch, cut, chop, mix, separate, paint, draw, create,
   weave, grow, perform, appoint, hear, blame, evaluate, marry,
   bark, breathe, laugh, cough, hiccup, blink, knock, tap,
   flash, flinch, dress, drown, glow, buzz, rumble, bleed,
   freeze, heat, bend, boil, rust, increase, straighten, flatten,
   open_, lengthen, widen, cool, warm, exist, appear, fidget,
   sit, stand, walk, swim, fly, roll, float, avoid,
   linger, rush, rain, charge, cost, fine, tip, pay,
   strike_, forgive, spare, deny, permit, assign, begrudge, bet,
   serve, teach, feed, show_, award, forward_, grant, offer,
   reserve, pass, hand, lend]

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

/-! ### Voice -/

/-- The passive, marked by the auxiliary *be* with the past participle,
`Verb.passiveParticiple`. -/
def passive : Voice := Voice.passive.marked [.free "be"]

/-- The active and the passive. -/
def voices : Finset Voice := {.active, passive}

end English
