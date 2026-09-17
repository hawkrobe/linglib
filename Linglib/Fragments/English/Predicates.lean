import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Verb.Basic
import Linglib.Syntax.Clause.Complementation
import Linglib.Morphology.Word.Basic
import Linglib.Fragments.English.Inflection

open Morphology (Word Features)

/-!
# English verbs

The English verb lexicon: each entry extends the cross-linguistic `Verb` (argument frames,
aspectual and semantic class, presupposition, causation and attitude facets) with the four
inflected forms, `Verb.realize` reading a cell and `Verb.mkRegular` deriving the forms of a
regular verb by the spelling rules of `Inflection.lean`. Entries are grouped by the
[levin-1993] class they carry, then by the paper whose classification they record; the
inventory `verbs` lists them all.

## Implementation notes

A citation form with several entries is a polysemous lexeme, told apart by `senseTag`
(*forget* the implicative and *forget* the rogative, *sweep* with and without an instrument
frame). An entry's `levinClass` is its class in Levin's member lists; a verb Levin does not
list carries `none` even when a paper groups it with a class. Where the sources describe a
reflex as dialect-variable or optional, the docstring says so.

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
  deriving Repr, BEq

/-- Construct a regular verb entry: inflected forms are computed from the
    citation form via English morphophonological rules.

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

/-- "run" — intransitive, no presupposition -/
def run : Verb where
  form := "run"
  form3sg := "runs"
  formPast := "ran"
  formPastPart := "run"
  formPresPart := "running"
  frames := [ArgumentFrame.intransitive]
  subjectEntailments := some activitySubjectProfile
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion
  root := { content := {
    force := {.moderate}
    agentControl := {.compatible}
  } }

/-- "arrive" — unaccusative intransitive -/
def arrive : Verb := .mkRegular {
  form := "arrive"
  frames := [ArgumentFrame.intransitive]
  subjectEntailments := some achievementSubjectProfile
  unaccusative := true
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .inherentlyDirectedMotion }

/-- "come" — Levin 51.1 inherently directed motion, like `arrive`. -/
def come : Verb where
  form := "come"
  form3sg := "comes"
  formPast := "came"
  formPastPart := "come"
  formPresPart := "coming"
  frames := [ArgumentFrame.intransitive]
  unaccusative := true
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .inherentlyDirectedMotion

/-- "eat" — transitive, implicit object is indefinite ("Have you eaten?") -/
def eat : Verb where
  form := "eat"
  form3sg := "eats"
  formPast := "ate"
  formPastPart := "eaten"
  formPresPart := "eating"
  frames := [ArgumentFrame.np]
  subjectEntailments := some accomplishmentSubjectProfile
  objectEntailments := some consumptionObject
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .eat
  root := { content := {
    force := {.low, .moderate}
    agentControl := {.compatible}
  } }

/-- "kick" — transitive -/
def kick : Verb := .mkRegular {
  form := "kick"
  frames := [ArgumentFrame.np]
  subjectEntailments := some accomplishmentSubjectProfile
  objectEntailments := some contactObject
  vendlerClass := some .activity
  levinClass := some .hit
  root := { content := {
    force := {.moderate, .high}
    direction := {.unidirectional}
    agentControl := {.neutral, .compatible}
  } } }

/-- "give" — ditransitive, alternates DOC/PP.
    Implicit goal is definite ([fillmore-1986]: pragmatically recoverable).
    Neither object can be implicit alone. -/
def give : Verb where
  form := "give"
  form3sg := "gives"
  formPast := "gave"
  formPastPart := "given"
  formPresPart := "giving"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment
  levinClass := some .give

/-- "put" — locative -/
def put : Verb where
  form := "put"
  form3sg := "puts"
  formPast := "put"
  formPastPart := "put"
  formPresPart := "putting"
  frames := [ArgumentFrame.np_pp]
  vendlerClass := some .achievement
  levinClass := some .put

/-- "weigh" — measure predicate selecting for mass/weight. -/
def weigh : Verb := .mkRegular {
  form := "weigh"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .measure }

/-- "cover" — motion/extent predicate selecting for distance. -/
def cover : Verb := .mkRegular {
  form := "cover"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc }

/-- "measure" — general measurement predicate. -/
def measure : Verb := .mkRegular {
  form := "measure"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .measure }

/-- "buy" — irregular transitive -/
def buy : Verb where
  form := "buy"
  form3sg := "buys"
  formPast := "bought"
  formPastPart := "bought"
  formPresPart := "buying"
  frames := [ArgumentFrame.np]
  subjectEntailments := some possessionTransfer.subjectProfile
  vendlerClass := some .accomplishment
  levinClass := some .getObtain

/-- "meet" — irregular transitive -/
def meet : Verb where
  form := "meet"
  form3sg := "meets"
  formPast := "met"
  formPastPart := "met"
  formPresPart := "meeting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement

/-- "set" — irregular; the base, past and past participle forms coincide. -/
def set_ : Verb where
  form := "set"
  form3sg := "sets"
  formPast := "set"
  formPastPart := "set"
  formPresPart := "setting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement

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
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp]
  subjectEntailments := some possessionTransfer.subjectProfile
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .accomplishment
  levinClass := some .give

/-- "leave" — transitive (also used intransitively with argument drop) -/
def leave : Verb where
  form := "leave"
  form3sg := "leaves"
  formPast := "left"
  formPastPart := "left"
  formPresPart := "leaving"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .leave

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
  levinClass := some .see

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
  factivity := some .semi }

/-- "notice" — semi-factive -/
def notice : Verb := .mkRegular {
  form := "notice"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)
  factivity := some .semi }

/-! ### Change of State -/

/-- "stop" — CoS cessation, presupposes activity was happening -/
def stop : Verb where
  form := "stop"
  form3sg := "stops"
  formPast := "stopped"
  formPastPart := "stopped"
  formPresPart := "stopping"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  cosType := some .cessation
  levinClass := some .aspectual

/-- "quit" — CoS cessation -/
def quit : Verb where
  form := "quit"
  form3sg := "quits"
  formPast := "quit"
  formPastPart := "quit"
  formPresPart := "quitting"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  cosType := some .cessation
  levinClass := some .aspectual

/-- "start" — CoS inception, presupposes activity wasn't happening -/
def start : Verb := .mkRegular {
  form := "start"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  cosType := some .inception
  levinClass := some .aspectual }

/-- "begin" — CoS inception -/
def begin_ : Verb where
  form := "begin"
  form3sg := "begins"
  formPast := "began"
  formPastPart := "begun"
  formPresPart := "beginning"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  cosType := some .inception
  levinClass := some .aspectual

/-- "continue" — CoS continuation, presupposes activity was happening -/
def continue_ : Verb := .mkRegular {
  form := "continue"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  cosType := some .continuation
  levinClass := some .aspectual }

/-- "keep" — CoS continuation -/
def keep : Verb where
  form := "keep"
  form3sg := "keeps"
  formPast := "kept"
  formPastPart := "kept"
  formPresPart := "keeping"
  frames := [ArgumentFrame.gerund]
  readings := [{ frame := ArgumentFrame.gerund, control := some .subjectControl }]
  vendlerClass := some .activity
  passivizable := false
  cosType := some .continuation
  levinClass := some .aspectual

/-! ### Implicative / Control -/

/-- "manage" — positive implicative: "managed to VP" entails "VP".
    Traditional analysis: agentive subject controls the complement.
    -/
def manage : Verb := .mkRegular {
  form := "manage"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  projectionBehavior := some .hole
  implicative := some .positive }

/-- "fail" — negative implicative: "failed to VP" entails "not VP" -/
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

/-- "persuade" — object control: "persuade X to VP" (X = agent of VP).
    Psychological attitude verb: causes the object to form an intention.
    Projects AUTHOR coordinate → obligatory *de se* ([landau-2015] table (36)). -/
def persuade : Verb := .mkRegular {
  form := "persuade"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "promise" — subject control with object: "promise X to VP".
    Desiderative attitude verb: the subject commits to a future action.
    [landau-2015] (5c) classifies it as desiderative → logophoric control. -/
def promise : Verb := .mkRegular {
  form := "promise"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : Verb := .mkRegular {
  form := "remember"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

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
  complementSig := some .mono }

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
  levinClass := some .want }

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
  attitude := some (.preferential (.degreeComparison .positive)) }

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
  attitude := some (.preferential (.degreeComparison .positive)) }

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
  attitude := some (.preferential (.degreeComparison .positive)) }

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
  levinClass := some .long

/-- "fear" — preferential attitude verb (Class 2: takes questions) -/
def fear : Verb := .mkRegular {
  form := "fear"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  levinClass := some .admire }

/-- "dread" — preferential attitude verb (Class 2: takes questions) -/
def dread : Verb := .mkRegular {
  form := "dread"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  levinClass := some .admire }

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

/-! ### Raising -/

/-- "seem" — raising verb (no theta role for subject, unaccusative) -/
def seem : Verb := .mkRegular {
  form := "seem"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .raising }]
  vendlerClass := some .state
  passivizable := false
  unaccusative := true }

/-! ### Causative (Periphrastic) -/

/-- "cause" — counterfactual dependence (necessity semantics) -/
def cause : Verb := .mkRegular {
  form := "cause"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .objectControl }]
  vendlerClass := some .accomplishment
  causative := some .cause
  levinClass := some .engender }

/-- "make" — direct sufficient guarantee -/
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

/-- "get" — causative use (persuasive causation) -/
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

/-- "kill" — thin lexical causative (kill = cause-to-die, COMPACT type). -/
def kill : Verb := .mkRegular {
  form := "kill"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .murder
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } } }

/-- "break" — thick lexical causative (Levin 45.1 Break Verbs; [embick-2009] break-class).
    Pure change-of-state verb: change in "material integrity"
    with no specification of how the change comes about ([levin-1993]:241). -/
def break_ : Verb where
  form := "break"
  form3sg := "breaks"
  formPast := "broke"
  formPastPart := "broken"
  formPresPart := "breaking"
  frames := [ArgumentFrame.np]
  unaccusative := false
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .break_
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
  frames := [ArgumentFrame.np]
  unaccusative := false
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causative := some .make
  levinClass := some .break_
  root := { content := {
    force := {.moderate, .high}
    direction := {.bidirectional, .unidirectional}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.separation}
    agentControl := {.neutral, .compatible}
    instrument := {.hands}
    patientDimensionality := {.twoD}
  } }

/-! ### Physical disturbance change-of-state verbs ([tham-2025]) -/

/-- "crack" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale (contra [rappaport-hovav-2014] two-point
    classification), but allows BOTH telic ("cracked in a minute") and atelic
    ("cracked for two days") readings. Compatible with *completely*, *partially*,
    *badly*. The verb is NOT a standard degree achievement: its variable telicity
    does not reduce to scale boundedness alone. -/
def crack : Verb := .mkRegular {
  form := "crack"
  frames := [ArgumentFrame.np]
  unaccusative := true
  vendlerClass := some .achievement
  degreeAchievementScale := some {
    dimension := .cracking,
    baseAdjective := some "cracked" }
  causative := some .make
  levinClass := some .break_ }

/-- "dent" — Levin 21.2 Carve verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale, compatible with *more dented*, *completely
    dented*, *badly dented*. -/
def dent : Verb := .mkRegular {
  form := "dent"
  frames := [ArgumentFrame.np]
  unaccusative := true
  vendlerClass := some .achievement
  degreeAchievementScale := some {
    dimension := .denting,
    baseAdjective := some "dented" }
  causative := some .make
  levinClass := some .carve }

/-- "scratch" — Levin 21.1 Cut verbs, a physical disturbance CoS verb for
    [tham-2025]: closed scale, compatible with *more scratched*, *completely
    scratched*, *badly scratched*. Levin also lists it among the wipe verbs
    (§10.4.1) and the swat verbs (§18.2) on its manner readings. -/
def scratch : Verb := .mkRegular {
  form := "scratch"
  frames := [ArgumentFrame.np]
  unaccusative := true
  vendlerClass := some .achievement
  degreeAchievementScale := some {
    dimension := .scratching,
    baseAdjective := some "scratched" }
  causative := some .make
  levinClass := some .cut }

/-- "shatter" — Levin 45.1 Break verbs. NOT a physical disturbance verb.
    Punctual, non-gradable: *shatter in two minutes* (after, not duration),
    #*shatter for two minutes*, ??*more shattered* ([tham-2025] (12)). -/
def shatter : Verb := .mkRegular {
  form := "shatter"
  frames := [ArgumentFrame.np]
  unaccusative := true
  vendlerClass := some .achievement
  causative := some .make
  levinClass := some .break_ }

/-- "burn" — thick lexical causative (manner = by fire/heat). -/
def burn : Verb := .mkRegular {
  form := "burn"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causative := some .make
  levinClass := some .otherCoS
  root := { content := {
    force := {.moderate, .high}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.totalDestruction, .deformation}
    agentControl := {.neutral, .compatible}
  } } }

/-- "destroy" — thin lexical causative (result-only, no manner). -/
def destroy : Verb := .mkRegular {
  form := "destroy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .destroy
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } } }

/-- "melt" — thick lexical causative (manner = by heat).
    Base transitive that productively takes DOC ("melt me some ice cream").
    Implicit obj is indefinite ("the ice cream melted" / "we're melting"). -/
def melt : Verb := .mkRegular {
  form := "melt"
  frames := [ArgumentFrame.np]
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causative := some .make
  levinClass := some .otherCoS
  root := { content := {
    force := {.low, .moderate}
    patientRobustness := {.moderate, .robust}
    resultGeometry := {.deformation}
    agentControl := {.compatible}
  } } }

/-! ### Thick and thin causatives ([martin-rose-nichols-2025]) -/

-- Entries for causative verbs classified by [martin-rose-nichols-2025] that don't
-- already have Fragment entries elsewhere (break_, burn, destroy, melt, kill,
-- cut, mix, start, stop already defined above).

/-- "activate" — thin causative, CoS without manner. -/
def activate : Verb := .mkRegular {
  form := "activate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "affect" — thin causative, general effect; Levin 31.1 Amuse verbs. -/
def affect : Verb := .mkRegular {
  form := "affect"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .amuse }

/-- "change" — thin causative, transformation (§26.6). -/
def change : Verb := .mkRegular {
  form := "change"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .turn }

/-- "damage" — thin causative, partial destruction. -/
def damage : Verb := .mkRegular {
  form := "damage"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "eliminate" — thin causative, removal; Levin 42.1 Murder verbs. -/
def eliminate : Verb := .mkRegular {
  form := "eliminate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .murder }

/-- "hurt" — thin causative, generic harm; Levin 40.8.3 Hurt verbs. -/
def hurt : Verb where
  form := "hurt"
  form3sg := "hurts"
  formPast := "hurt"
  formPastPart := "hurt"
  formPresPart := "hurting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .hurt

/-- "restore" — thin causative, Levin 13.2 Contribute verbs. -/
def restore : Verb := .mkRegular {
  form := "restore"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .contribute }

/-- "trigger" — thin causative, engender class (§27). -/
def trigger : Verb := .mkRegular {
  form := "trigger"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .engender }

/-- "bury" — thick causative (state), concealment.
    Levin's concealment class (§16) does not list *bury*. -/
def bury : Verb := .mkRegular {
  form := "bury"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "drop" — thick causative, Levin 45.6 calibratable change-of-state verbs. -/
def drop : Verb := .mkRegular {
  form := "drop"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .calibratableCoS }

/-- "lift" — thick causative, Levin 9.4 verbs of putting with a specified
    direction. -/
def lift : Verb := .mkRegular {
  form := "lift"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .putDirection }

/-- "lock" — thick causative, caused secured state.
    Levin lists *lock* only among the tape verbs (§22.4). -/
def lock : Verb := .mkRegular {
  form := "lock"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-- "shut" — thick causative, caused closed state (§45.4). -/
def shut : Verb where
  form := "shut"
  form3sg := "shuts"
  formPast := "shut"
  formPastPart := "shut"
  formPresPart := "shutting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS

/-- "spread" — thick causative, spray/load class (§9.7). -/
def spread : Verb where
  form := "spread"
  form3sg := "spreads"
  formPast := "spread"
  formPastPart := "spread"
  formPresPart := "spreading"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .sprayLoad

/-- "stretch" — thick causative, Levin 45.4 other change-of-state verbs. -/
def stretch : Verb := .mkRegular {
  form := "stretch"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

/-- "switch" — thick causative, CoS.
    Levin's change-of-state lists do not include *switch*. -/
def switch : Verb := .mkRegular {
  form := "switch"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
 }

/-! ### Other -/

/-- "devour" — transitive, no presupposition -/
def devour : Verb := .mkRegular {
  form := "devour"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .devour
  root := { content := {
    force := {.moderate, .high}
    agentControl := {.neutral}
  } } }

/-- "drink" — Levin 39.1 Eat verbs. -/
def drink : Verb where
  form := "drink"
  form3sg := "drinks"
  formPast := "drank"
  formPastPart := "drunk"
  formPresPart := "drinking"
  frames := [ArgumentFrame.np]
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .eat

/-- "read" — transitive, no presupposition -/
def read : Verb where
  form := "read"
  form3sg := "reads"
  formPast := "read"
  formPastPart := "read"
  formPresPart := "reading"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .inc

/-- "build" — creation verb, strictly incremental theme.
    Base transitive that productively takes DOC ("build us a house"). -/
def build : Verb where
  form := "build"
  form3sg := "builds"
  formPast := "built"
  formPastPart := "built"
  formPresPart := "building"
  frames := [ArgumentFrame.np]
  subjectEntailments := some accomplishmentSubjectProfile
  objectEntailments := some creationObject
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .build

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
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp]
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .imageCreation

/-- "sweep" — motion + sustained contact, variable agentivity (default sense). -/
def sweep : Verb where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  subjectEntailments := some wipeManner.subjectProfile
  passivizable := true
  levinClass := some .wipe
  root := { content := {
    force := {.low, .moderate}
    direction := {.unidirectional}
    agentControl := {.compatible}
  } }

/-- "sweep" instrument sense — obligatorily agentive, broom lexicalized. -/
def sweep_instr : Verb where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  subjectEntailments := some wipeInstrument.subjectProfile
  passivizable := true
  senseTag := .instrumental
  levinClass := some .wipe
  root := { content := {
    force := {.low, .moderate}
    direction := {.unidirectional}
    agentControl := {.compatible}
  } }

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
  levinClass := some .say

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
  frames := [ArgumentFrame.finiteClause, ArgumentFrame.np_np]
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClass := some .tell

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : Verb := .mkRegular {
  form := "claim"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClass := some .say }

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
  levinClass := some .say }

/-- "acknowledge" — optionally factive communication verb
    Levin lists *acknowledge* only among the appoint verbs (§29.1), a different frame. -/
def acknowledge : Verb := .mkRegular {
  form := "acknowledge"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
 }

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

/-- "announce" — communication verb -/
def announce : Verb := .mkRegular {
  form := "announce"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say }

/-- "confess" — optionally factive communication verb -/
def confess : Verb := .mkRegular {
  form := "confess"
  frames := [ArgumentFrame.finiteClause]
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say }

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
  levinClass := some .say }

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
  vendlerClass := some .achievement }

/-- "demonstrate" — evidential verb -/
def demonstrate : Verb := .mkRegular {
  form := "demonstrate"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement }

/-- "establish" — evidential verb -/
def establish : Verb := .mkRegular {
  form := "establish"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement }

/-- "prove" — evidential verb -/
def prove : Verb := .mkRegular {
  form := "prove"
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .achievement }

/-! ### Manner of Speaking (Levin 37.3) -/

/-! Manner-of-speaking (MoS) verbs specify *how* something is said.
    [storment-2026] shows these divide into two classes:
    - **QI-permitting** (unaccusative): whisper, murmur, mumble, mutter, shout,
      cry, scream, shriek, yell, groan, grumble, hiss, sigh, whimper, snap
    - **Non-QI** (unergative): speak, talk -/

/-- "whisper" — MoS verb, permits quotative inversion (unaccusative) -/
def whisper : Verb := .mkRegular {
  form := "whisper"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "murmur" — MoS verb, permits quotative inversion (unaccusative) -/
def murmur : Verb := .mkRegular {
  form := "murmur"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "shout" — MoS verb, permits quotative inversion (unaccusative) -/
def shout : Verb := .mkRegular {
  form := "shout"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "cry" — MoS verb, permits quotative inversion (unaccusative) -/
def cry : Verb := .mkRegular {
  form := "cry"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "scream" — MoS verb, permits quotative inversion (unaccusative) -/
def scream : Verb := .mkRegular {
  form := "scream"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "mumble" — MoS verb, permits quotative inversion (unaccusative) -/
def mumble : Verb := .mkRegular {
  form := "mumble"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "mutter" — MoS verb, permits quotative inversion (unaccusative) -/
def mutter : Verb := .mkRegular {
  form := "mutter"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "shriek" — MoS verb, permits quotative inversion (unaccusative) -/
def shriek : Verb := .mkRegular {
  form := "shriek"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "yell" — MoS verb, permits quotative inversion (unaccusative) -/
def yell : Verb := .mkRegular {
  form := "yell"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "groan" — MoS verb, permits quotative inversion (unaccusative) -/
def groan : Verb := .mkRegular {
  form := "groan"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "grumble" — MoS verb, permits quotative inversion (unaccusative) -/
def grumble : Verb := .mkRegular {
  form := "grumble"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "hiss" — MoS verb, permits quotative inversion (unaccusative) -/
def hiss : Verb := .mkRegular {
  form := "hiss"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "sigh" — a manner-of-speaking-like verb, permits quotative inversion (unaccusative)
    Levin 40.2 verbs of nonverbal expression. -/
def sigh : Verb := .mkRegular {
  form := "sigh"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .nonverbalExpression }

/-- "whimper" — MoS verb, permits quotative inversion (unaccusative) -/
def whimper : Verb := .mkRegular {
  form := "whimper"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "snap" — MoS verb, permits quotative inversion (unaccusative) -/
def snap : Verb := .mkRegular {
  form := "snap"
  speechActVerb := true
  frames := [ArgumentFrame.finiteClause]
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

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
  levinClass := some .talk

/-- "talk" — agentive communication verb, blocks quotative inversion (unergative)
    Levin 37.5 Talk verbs. -/
def talk : Verb := .mkRegular {
  form := "talk"
  speechActVerb := true
  frames := [ArgumentFrame.intransitive]
  vendlerClass := some .activity
  passivizable := false
  levinClass := some .talk }

/-! ### Question-Embedding -/

/-- "wonder" — embeds questions only -/
def wonder : Verb := .mkRegular {
  form := "wonder"
  frames := [ArgumentFrame.question]
  vendlerClass := some .state
  opaqueContext := true }

/-- "ask" — embeds questions -/
def ask : Verb := .mkRegular {
  form := "ask"
  speechActVerb := true
  frames := [ArgumentFrame.question]
  vendlerClass := some .achievement }

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : Verb := .mkRegular {
  form := "investigate"
  frames := [ArgumentFrame.question]
  vendlerClass := some .activity
  levinClass := some .search }

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
  senseTag := .rogative }

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

/-- "dare" — positive implicative with prerequisite presupposition: courage.
    "Ana dared to enter the cave" → "Ana entered the cave."
    Presupposes that daring/courageous action was required for complement
    realization ([nadathur-2023-implicatives] §5.2, ex. 3–4, 26). -/
def dare : Verb := .mkRegular {
  form := "dare"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

/-- "bother" — positive implicative with prerequisite presupposition: engagement.
    "He bothered to answer" → "He answered."
    Presupposes that overcoming apathy/effort was required
    ([nadathur-2023-implicatives] §2, ex. 10, 28). -/
def bother : Verb := .mkRegular {
  form := "bother"
  frames := [ArgumentFrame.infinitival]
  readings := [{ frame := ArgumentFrame.infinitival, control := some .subjectControl }]
  vendlerClass := some .achievement
  passivizable := false
  implicative := some .positive }

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
  implicative := some .negative }

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
  implicative := some .positive }

/-! ### Agent-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.2 (admire). Subject = experiencer, object = stimulus.
    NP1 (subject) IC bias. -/

/-- "enjoy" — AgExp verb (experiencer-subject) -/
def enjoy : Verb := .mkRegular {
  form := "enjoy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "like" — AgExp verb (experiencer-subject) -/
def like : Verb := .mkRegular {
  form := "like"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "love" — AgExp verb (experiencer-subject) -/
def love : Verb := .mkRegular {
  form := "love"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : Verb := .mkRegular {
  form := "hate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : Verb := .mkRegular {
  form := "admire"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "envy" — AgExp verb (experiencer-subject).
    DOC-only ditransitive ("He envies me the car"). Implicit goal is
    definite (familiar). Implicit second obj is indefinite. -/
def envy : Verb := .mkRegular {
  form := "envy"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .state
  levinClass := some .admire }

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : Verb := .mkRegular {
  form := "respect"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "value" — AgExp verb (experiencer-subject) -/
def value : Verb := .mkRegular {
  form := "value"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : Verb := .mkRegular {
  form := "fear"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : Verb := .mkRegular {
  form := "dread"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .admire }

/-! ### Stimulus-experiencer verbs ([solstad-bott-2024]) -/

/-! [levin-1993] class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def frighten : Verb := .mkRegular {
  form := "frighten"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "amuse" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def amuse : Verb := .mkRegular {
  form := "amuse"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "fascinate" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def fascinate : Verb := .mkRegular {
  form := "fascinate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "irritate" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def irritate : Verb := .mkRegular {
  form := "irritate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "annoy" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def annoy : Verb := .mkRegular {
  form := "annoy"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "bore" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def bore : Verb := .mkRegular {
  form := "bore"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "charm" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def charm : Verb := .mkRegular {
  form := "charm"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "impress" — StimExp verb (stimulus-subject, eventive: [kim-2024] UPH) -/
def impress : Verb := .mkRegular {
  form := "impress"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "concern" — stative Class II psych verb ([kim-2024] UPH, internal cause) -/
def concern : Verb := .mkRegular {
  form := "concern"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "interest" — stative Class II psych verb ([kim-2024] UPH, internal cause) -/
def interest : Verb := .mkRegular {
  form := "interest"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : Verb := .mkRegular {
  form := "surprise"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : Verb := .mkRegular {
  form := "scare"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : Verb := .mkRegular {
  form := "delight"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : Verb := .mkRegular {
  form := "embarrass"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : Verb := .mkRegular {
  form := "upset"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : Verb := .mkRegular {
  form := "disgust"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : Verb := .mkRegular {
  form := "shock"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : Verb := .mkRegular {
  form := "confuse"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : Verb := .mkRegular {
  form := "disappoint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "worry" (eventive) — Class II, external cause. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : Verb := .mkRegular {
  form := "worry"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "worry" (stative) — Class II, internal cause. "The situation worries John."
    [kim-2024] UPH: same theta grid as worry_eventive, different causal source. -/
def worry_stative : Verb := .mkRegular {
  form := "worry"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "please" — stative Class II ([kim-2024] UPH, internal cause).
    "The idea pleases John." Related to B&R Class III It. *piacere*. -/
def please_psych : Verb := .mkRegular {
  form := "please"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "trouble" — stative Class II ([kim-2024] UPH, internal cause).
    "The thought troubles John." -/
def trouble : Verb := .mkRegular {
  form := "trouble"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "puzzle" — stative Class II ([kim-2024] UPH, internal cause).
    "The problem puzzles John." -/
def puzzle : Verb := .mkRegular {
  form := "puzzle"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-! ### Agent-patient verbs ([solstad-bott-2024]) -/

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : Verb := .mkRegular {
  form := "chase"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .chase }

/-- "hit" — AgPat verb (Levin 18.1) -/
def hit : Verb where
  form := "hit"
  form3sg := "hits"
  formPast := "hit"
  formPastPart := "hit"
  formPresPart := "hitting"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .hit

/-- "push" — AgPat verb (Levin 12) -/
def push : Verb := .mkRegular {
  form := "push"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pushPull }

/-- "pull" — AgPat verb (Levin 12) -/
def pull : Verb := .mkRegular {
  form := "pull"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pushPull }

/-- "shove" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def shove : Verb := .mkRegular {
  form := "shove"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "tug" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def tug : Verb where
  form := "tug"
  form3sg := "tugs"
  formPast := "tugged"
  formPastPart := "tugged"
  formPresPart := "tugging"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .pushPull

/-- "yank" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def yank : Verb := .mkRegular {
  form := "yank"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "jerk" — verb of exerting force (Levin 12, [levin-2026] (31)) -/
def jerk : Verb := .mkRegular {
  form := "jerk"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "wrench" — verb of exerting force for [levin-2026] (31); not among the
    members of Levin's §12. -/
def wrench : Verb := .mkRegular {
  form := "wrench"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
 }

/-- "fling" — Levin 17.1 Throw verbs; a verb of exerting force for
    [levin-2026] (31). Irregular past. -/
def fling : Verb where
  form := "fling"
  form3sg := "flings"
  formPast := "flung"
  formPastPart := "flung"
  formPresPart := "flinging"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity

/-- "slam" — Levin 17.1 Throw verbs; a hitting verb for [levin-2026] (32a).
    Irregular doubling. -/
def slam : Verb where
  form := "slam"
  form3sg := "slams"
  formPast := "slammed"
  formPastPart := "slammed"
  formPresPart := "slamming"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .throw

/-- "punch" — Levin 18.2 Swat verbs; a hitting verb for [levin-2026] (32a). -/
def punch : Verb := .mkRegular {
  form := "punch"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .swat }

/-- "smack" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def smack : Verb := .mkRegular {
  form := "smack"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "thump" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def thump : Verb := .mkRegular {
  form := "thump"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "bang" — verb of surface contact, hitting (Levin 18.1,
    [levin-2026] (32a)) -/
def bang : Verb := .mkRegular {
  form := "bang"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "thrash" — Levin 18.3 Spank verbs; a hitting verb for [levin-2026] (32a). -/
def thrash : Verb := .mkRegular {
  form := "thrash"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .spank }

/-- "hammer" — Levin 18.1 Hit verbs. -/
def hammer : Verb := .mkRegular {
  form := "hammer"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "scrape" — verb of surface contact, wiping (Levin 10.4,
    [levin-2026] (32b)). In intr-push-open, enters through
    surface-contact sense, not removing sense. -/
def scrape : Verb := .mkRegular {
  form := "scrape"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .wipe }

/-- "wipe" — Levin 10.4 Wipe verbs, manner subclass. -/
def wipe : Verb := .mkRegular {
  form := "wipe"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  levinClass := some .wipe }

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : Verb where
  form := "carry"
  form3sg := "carries"
  formPast := "carried"
  formPastPart := "carried"
  formPresPart := "carrying"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .carry

/-- "drag" — AgPat verb (Levin 11.4/12) -/
def drag : Verb where
  form := "drag"
  form3sg := "drags"
  formPast := "dragged"
  formPastPart := "dragged"
  formPresPart := "dragging"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .carry

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : Verb := .mkRegular {
  form := "call"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity }

/-! ### Putting (§ 9) -/

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : Verb := .mkRegular {
  form := "place"
  frames := [ArgumentFrame.np_pp]
  vendlerClass := some .achievement
  levinClass := some .put }

/-- "water" — Levin 9.9 Butter verbs (denominal putting). -/
def water : Verb := .mkRegular {
  form := "water"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity }

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : Verb := .mkRegular {
  form := "pour"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pour }

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : Verb := .mkRegular {
  form := "spray"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .sprayLoad }

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : Verb := .mkRegular {
  form := "load"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .sprayLoad }

/-! ### Removing (§ 10) -/

/-- "remove" — Levin 10.1 Remove verbs. -/
def remove : Verb := .mkRegular {
  form := "remove"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .remove }

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : Verb := .mkRegular {
  form := "clean"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    dimension := .cleanliness,
    baseAdjective := some "clean" }
  verbIncClass := some .sinc
  levinClass := some .clear }

/-- "steal" — Levin 10.5 Steal verbs. -/
def steal : Verb where
  form := "steal"
  form3sg := "steals"
  formPast := "stole"
  formPastPart := "stolen"
  formPresPart := "stealing"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .steal

/-! ### Sending and Carrying (§ 11) -/

/-- "send" — Levin 11.1 Send verbs. Alternates DOC/PP.
    Goal does not entail possession (prospective). Neither object implicit alone. -/
def send : Verb where
  form := "send"
  form3sg := "sends"
  formPast := "sent"
  formPastPart := "sent"
  formPresPart := "sending"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np]
  implicitGoal := some .def
  vendlerClass := some .accomplishment
  levinClass := some .send

/-- "drive" — Levin 11.5 Drive verbs (vehicle-mediated motion). -/
def drive : Verb where
  form := "drive"
  form3sg := "drives"
  formPast := "drove"
  formPastPart := "driven"
  formPresPart := "driving"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .drive

/-! ### Change of Possession (§ 13) -/

/-- "donate" — Levin 13.2 Contribute verbs. -/
def donate : Verb := .mkRegular {
  form := "donate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .contribute }

/-- "obtain" — Levin 13.5.2 Obtain verbs. -/
def obtain : Verb := .mkRegular {
  form := "obtain"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .getObtain }

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : Verb := .mkRegular {
  form := "trade"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .exchange }

/-! ### Learn, Hold, Conceal (§ 14–16) -/

/-- "learn" — Levin 14 Learn verbs. -/
def learn : Verb := .mkRegular {
  form := "learn"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .learn }

/-- "hold" — Levin 15.1 Hold verbs. Stative. -/
def hold : Verb where
  form := "hold"
  form3sg := "holds"
  formPast := "held"
  formPastPart := "held"
  formPresPart := "holding"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .hold

/-- "hide" — Levin 16 Conceal verbs. -/
def hide : Verb where
  form := "hide"
  form3sg := "hides"
  formPast := "hid"
  formPastPart := "hidden"
  formPresPart := "hiding"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .conceal

/-! ### Throwing (§ 17) -/

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. Alternates DOC/PP.
    Implicit DO in PP frame only (definite). -/
def throw : Verb where
  form := "throw"
  form3sg := "throws"
  formPast := "threw"
  formPastPart := "thrown"
  formPresPart := "throwing"
  frames := [ArgumentFrame.np, ArgumentFrame.np_np]
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .achievement
  levinClass := some .throw

/-! ### Contact (§ 19–20) -/

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : Verb := .mkRegular {
  form := "poke"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .poke }

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : Verb := .mkRegular {
  form := "touch"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .touch }

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
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .cut
  root := { content := {
    resultGeometry := {.surfaceBreach}
    instrument := {.sharpBlade}
  } }

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : Verb where
  form := "chop"
  form3sg := "chops"
  formPast := "chopped"
  formPastPart := "chopped"
  formPresPart := "chopping"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .carve

/-! ### Combining and Separating (§ 22–23) -/

/-- "mix" — Levin 22.1 Mix verbs. Incremental by proportion combined. -/
def mix : Verb := .mkRegular {
  form := "mix"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .mix }

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : Verb := .mkRegular {
  form := "separate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .separate }

/-! ### Coloring and Image Creation (§ 24–25) -/

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : Verb := .mkRegular {
  form := "paint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .color }

/-- "draw" — Levin 25 Image Creation verbs. Incremental by extent. -/
def draw : Verb where
  form := "draw"
  form3sg := "draws"
  formPast := "drew"
  formPastPart := "drawn"
  formPresPart := "drawing"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .imageCreation

/-! ### Creation and Transformation (§ 26) -/

/-- "create" — Levin 26.4 Create verbs. -/
def create : Verb := .mkRegular {
  form := "create"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .create }

/-- "weave" — Levin 26.1 Build verbs. -/
def weave : Verb where
  form := "weave"
  form3sg := "weaves"
  formPast := "wove"
  formPastPart := "woven"
  formPresPart := "weaving"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .build

/-- "grow" — Levin 26.2 Grow verbs. Incremental by size. -/
def grow : Verb where
  form := "grow"
  form3sg := "grows"
  formPast := "grew"
  formPastPart := "grown"
  formPresPart := "growing"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .grow

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : Verb := .mkRegular {
  form := "perform"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .performance }

/-! ### Predicative Complements (§ 29) -/

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : Verb := .mkRegular {
  form := "appoint"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .appoint }

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
  levinClass := some .see

/-! ### Judgment and Assessment (§ 33–34) -/

/-- "blame" — a judgment verb by sense, absent from Levin's §33 member lists
    and named only for the blame alternation (§2.10). -/
def blame : Verb := .mkRegular {
  form := "blame"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
 }

/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : Verb := .mkRegular {
  form := "evaluate"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .assessment }

/-! ### Social Interaction (§ 36) -/

/-- "marry" — Levin 36 Social Interaction verbs. -/
def marry : Verb where
  form := "marry"
  form3sg := "marries"
  formPast := "married"
  formPastPart := "married"
  formPresPart := "marrying"
  frames := [ArgumentFrame.np]
  vendlerClass := some .achievement
  levinClass := some .socialInteraction

/-! ### Animal Sounds (§ 38) -/

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : Verb := .mkRegular {
  form := "bark"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .animalSound }

/-! ### Body (§ 40–41) -/

/-- "breathe" — Levin 40.1 Body Process verbs. -/
def breathe : Verb := .mkRegular {
  form := "breathe"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .bodyProcess }

/-- "laugh" — Levin 40.2 Nonverbal Expression verbs. -/
def laugh : Verb := .mkRegular {
  form := "laugh"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity }

/-- "cough" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary event, no result state ([smith-1997] §2.4.3). -/
def cough : Verb := .mkRegular {
  form := "cough"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .bodyProcess }

/-- "hiccup" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary body event ([smith-1997] §2.4.3). -/
def hiccup : Verb := .mkRegular {
  form := "hiccup"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .bodyProcess }

/-- "blink" — semelfactive: a single instantaneous eye movement, by [smith-1997]'s
    characterization of the class. Levin lists *blink (eye)* among the wink verbs (§40.3.1)
    and *blink* among the light-emission verbs (§43.1). -/
def blink : Verb := .mkRegular {
  form := "blink"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
 }

/-- "knock" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single percussive contact event, [smith-1997]'s standard
    example of the class. -/
def knock : Verb := .mkRegular {
  form := "knock"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .hit }

/-- "tap" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single light percussive contact event ([smith-1997] §2.4.3). -/
def tap : Verb := .mkRegular {
  form := "tap"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .hit }

/-- "flash" — Levin 43.1 Light Emission verbs.
    Semelfactive: single instantaneous light event, by [smith-1997]'s
    characterization of the class. -/
def flash : Verb := .mkRegular {
  form := "flash"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .lightEmission }

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : Verb := .mkRegular {
  form := "flinch"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .flinch }

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : Verb := .mkRegular {
  form := "dress"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  levinClass := some .dress }

/-! ### Killing (§ 42) -/

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : Verb := .mkRegular {
  form := "drown"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .poison }

/-! ### Emission (§ 43) -/

/-- "glow" — Levin 43.1 Light Emission verbs. -/
def glow : Verb := .mkRegular {
  form := "glow"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .state
  unaccusative := true
  levinClass := some .lightEmission }

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : Verb := .mkRegular {
  form := "buzz"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .soundEmission }

/-- "rumble" — Levin 43.2 Sound Emission verbs. -/
def rumble : Verb := .mkRegular {
  form := "rumble"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .soundEmission }

/-- "bleed" — Levin 43.4 Substance Emission verbs. -/
def bleed : Verb where
  form := "bleed"
  form3sg := "bleeds"
  formPast := "bled"
  formPastPart := "bled"
  formPresPart := "bleeding"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .substanceEmission

/-! ### Change of State (§ 45) -/

/-- "freeze" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def freeze : Verb where
  form := "freeze"
  form3sg := "freezes"
  formPast := "froze"
  formPastPart := "frozen"
  formPresPart := "freezing"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .otherCoS

/-- "heat" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def heat : Verb := .mkRegular {
  form := "heat"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .otherCoS }

/-- "bend" — Levin 45.2 Bend verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (straight → bent, has maximal endpoint). -/
def bend : Verb where
  form := "bend"
  form3sg := "bends"
  formPast := "bent"
  formPastPart := "bent"
  formPresPart := "bending"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    dimension := .curvature }
  causative := some .make
  levinClass := some .bend

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : Verb := .mkRegular {
  form := "boil"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    dimension := .boiling,
    baseAdjective := some "hot" }
  causative := some .make
  levinClass := some .cooking }

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : Verb := .mkRegular {
  form := "rust"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  unaccusative := true
  vendlerClass := some .activity
  degreeAchievementScale := some {
    dimension := .corrosion }
  levinClass := some .entitySpecificCoS }

/-- "increase" — Levin 45.6 Calibratable CoS verbs (degree achievements).
    Degree achievement: open scale (no maximum quantity). -/
def increase : Verb := .mkRegular {
  form := "increase"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  degreeAchievementScale := some {
    dimension := .quantity }
  levinClass := some .calibratableCoS }

/-! ### Degree achievement verb pairs ([kennedy-2007]) -/

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : Verb := .mkRegular {
  form := "straighten"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    dimension := .straightness,
    baseAdjective := some "straight" }
  levinClass := some .otherCoS }

/-- "flatten" — Closed-scale degree achievement (base adj: flat).
    Accomplishment: "flattened the dough in 2 minutes." -/
def flatten : Verb := .mkRegular {
  form := "flatten"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    dimension := .flatness,
    baseAdjective := some "flat" }
  levinClass := some .otherCoS }

/-- "open" — Closed-scale degree achievement (base adj: open, closed scale).
    Accomplishment: "opened the door in 3 seconds." -/
def open_ : Verb := .mkRegular {
  form := "open"
  frames := [ArgumentFrame.np]
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    dimension := .openness,
    baseAdjective := some "open" }
  levinClass := some .otherCoS }

/-- "lengthen" — Open-scale degree achievement (base adj: long, open scale).
    Activity: "lengthened the rope for hours." -/
def lengthen : Verb := .mkRegular {
  form := "lengthen"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  degreeAchievementScale := some {
    dimension := .length,
    baseAdjective := some "long" }
  levinClass := some .otherCoS }

/-- "widen" — Open-scale degree achievement (base adj: wide, open scale).
    Activity: "widened the road for months." -/
def widen : Verb := .mkRegular {
  form := "widen"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  degreeAchievementScale := some {
    dimension := .width,
    baseAdjective := some "wide" }
  levinClass := some .otherCoS }

/-- "cool" — Open-scale degree achievement (base adj: cool, open scale).
    Activity: "cooled for an hour." -/
def cool : Verb := .mkRegular {
  form := "cool"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  degreeAchievementScale := some {
    dimension := .temperature,
    baseAdjective := some "cool" }
  levinClass := some .otherCoS }

/-- "warm" — Open-scale degree achievement (base adj: warm, open scale).
    Activity: "warmed for an hour." -/
def warm : Verb := .mkRegular {
  form := "warm"
  frames := [ArgumentFrame.np]
  vendlerClass := some .activity
  degreeAchievementScale := some {
    dimension := .temperature,
    baseAdjective := some "warm" }
  levinClass := some .otherCoS }

/-! ### Existence, Appearance, Position (§ 47–50) -/

/-- "exist" — Levin 47.1 Exist verbs. Pure state. -/
def exist : Verb := .mkRegular {
  form := "exist"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .state
  unaccusative := true
  levinClass := some .exist }

/-- "appear" — Levin 48.1 Appear verbs. Punctual emergence. -/
def appear : Verb := .mkRegular {
  form := "appear"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .achievement
  unaccusative := true
  levinClass := some .appear }

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : Verb := .mkRegular {
  form := "fidget"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .bodyInternalMotion }

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
  levinClass := some .assumePosition

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
  levinClass := some .assumePosition

/-! ### Motion (§ 51) -/

/-- "walk" — Levin 51.3 Manner of Motion verbs. -/
def walk : Verb := .mkRegular {
  form := "walk"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion }

/-- "swim" — Levin 51.3 Manner of Motion verbs. -/
def swim : Verb where
  form := "swim"
  form3sg := "swims"
  formPast := "swam"
  formPastPart := "swum"
  formPresPart := "swimming"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion

/-- "fly" — Levin 51.4 Vehicle Motion verbs. -/
def fly : Verb where
  form := "fly"
  form3sg := "flies"
  formPast := "flew"
  formPastPart := "flown"
  formPresPart := "flying"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .vehicleMotion

/-- "roll" — Levin 51.3.1 Roll verbs (manner of motion). -/
def roll : Verb := .mkRegular {
  form := "roll"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion }

/-- "float" — Levin 51.3.1 Roll verbs (manner of motion). -/
def float : Verb := .mkRegular {
  form := "float"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion }

/-! ### Avoid, Linger, Rush (§ 52–53) -/

/-- "avoid" — Levin 52 Avoid verbs. Stative. -/
def avoid : Verb := .mkRegular {
  form := "avoid"
  frames := [ArgumentFrame.np]
  vendlerClass := some .state
  levinClass := some .avoid }

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : Verb := .mkRegular {
  form := "linger"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .linger }

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : Verb := .mkRegular {
  form := "rush"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .rush }

/-! ### Weather (§ 57) -/

/-- "rain" — Levin 57 Weather verbs. Expletive subject. -/
def rain : Verb := .mkRegular {
  form := "rain"
  frames := [ArgumentFrame.intransitive]
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .weather }

/-! ### Ditransitive verbs and implicit arguments ([bruening-2021]) -/

/-! Ditransitive verbs classified by their implicit argument behavior,
    following [bruening-2021] Table (56). The classification is
    theory-neutral: it records surface optionality and interpretation
    without committing to a specific structural analysis. -/

-- DOC-only verbs (no PP frame alternant)

/-- "charge" — DOC-only. Implicit second obj indef, implicit goal def (addressee). -/
def charge : Verb := .mkRegular {
  form := "charge"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "cost" — DOC-only. Implicit second obj indef, implicit goal def. -/
def cost : Verb := .mkRegular {
  form := "cost"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .state }

/-- "fine" — DOC-only. Implicit second obj indef, implicit goal def. -/
def fine : Verb := .mkRegular {
  form := "fine"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .indef
  vendlerClass := some .accomplishment }

/-- "tip" — DOC-only. Implicit second obj indef, implicit goal def (unique). -/
def tip : Verb where
  form := "tip"
  form3sg := "tips"
  formPast := "tipped"
  formPastPart := "tipped"
  formPresPart := "tipping"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "pay" — DOC-only. Implicit second obj indef, implicit goal def. -/
def pay : Verb where
  form := "pay"
  form3sg := "pays"
  formPast := "paid"
  formPastPart := "paid"
  formPresPart := "paying"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "strike" — DOC-only. Implicit second obj indef, implicit goal def (familiar). -/
def strike_ : Verb where
  form := "strike"
  form3sg := "strikes"
  formPast := "struck"
  formPastPart := "struck"
  formPresPart := "striking"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .achievement
  senseTag := .default

/-- "forgive" — DOC-only. Implicit second obj def, implicit goal def (addressee). -/
def forgive : Verb where
  form := "forgive"
  form3sg := "forgives"
  formPast := "forgave"
  formPastPart := "forgiven"
  formPresPart := "forgiving"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .def
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "spare" — DOC-only. Implicit second obj def, no implicit goal. -/
def spare : Verb := .mkRegular {
  form := "spare"
  frames := [ArgumentFrame.np_np]
  implicitObj := some .def
  vendlerClass := some .accomplishment }

/-- "deny" — DOC-only. Implicit goal def; second object obligatory
    ([bruening-2021] Table 56 row 3 col 1, ex. (32d) p. 1032). -/
def deny : Verb where
  form := "deny"
  form3sg := "denies"
  formPast := "denied"
  formPastPart := "denied"
  formPresPart := "denying"
  frames := [ArgumentFrame.np_np]
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "permit" — DOC-only. Implicit goal def (addressee); second object
    obligatory ([bruening-2021] Table 56 row 3 col 1, ex. (32e) p. 1032). -/
def permit : Verb where
  form := "permit"
  form3sg := "permits"
  formPast := "permitted"
  formPastPart := "permitted"
  formPresPart := "permitting"
  frames := [ArgumentFrame.np_np]
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "assign" — alternating (DOC + PP). Implicit goal definite; the second
    object is obligatory, Pesetsky's observation as [bruening-2021] report it. -/
def assign : Verb := .mkRegular {
  form := "assign"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

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

-- Alternating verbs (both DOC and PP frame)

/-- "serve" — alternates DOC/PP. Implicit second obj indef (DOC).
    Implicit goal def (PP). -/
def serve : Verb := .mkRegular {
  form := "serve"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "teach" — alternates DOC/PP. Implicit goal indef (PP).
    When both implicit, both are indefinite. -/
def teach : Verb where
  form := "teach"
  form3sg := "teaches"
  formPast := "taught"
  formPastPart := "taught"
  formPresPart := "teaching"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitObj := some .indef
  implicitGoal := some .indef
  vendlerClass := some .activity

/-- "feed" — alternates DOC/PP. Implicit second obj indef (DOC).
    No implicit goal. -/
def feed : Verb where
  form := "feed"
  form3sg := "feeds"
  formPast := "fed"
  formPastPart := "fed"
  formPresPart := "feeding"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitObj := some .indef
  vendlerClass := some .activity

/-- "show" — alternates DOC/PP. Implicit second obj def. No implicit goal. -/
def show_ : Verb where
  form := "show"
  form3sg := "shows"
  formPast := "showed"
  formPastPart := "shown"
  formPresPart := "showing"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitObj := some .def
  vendlerClass := some .accomplishment

/-- "award" — alternates DOC/PP. Implicit goal def (PP). -/
def award : Verb := .mkRegular {
  form := "award"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "forward" — alternates DOC/PP. Implicit goal def (PP). -/
def forward_ : Verb := .mkRegular {
  form := "forward"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "grant" — alternates DOC/PP. Implicit goal def (PP). -/
def grant : Verb := .mkRegular {
  form := "grant"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "offer" — alternates DOC/PP. Implicit goal def (PP). -/
def offer : Verb := .mkRegular {
  form := "offer"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "reserve" — alternates DOC/PP. Implicit goal def (PP). -/
def reserve : Verb := .mkRegular {
  form := "reserve"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "pass" — alternates DOC/PP. Implicit DO def in PP frame only. -/
def pass : Verb := .mkRegular {
  form := "pass"
  frames := [ArgumentFrame.np, ArgumentFrame.np_pp]
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .accomplishment
  levinClass := some .give }

-- Alternating verbs with no implicit arguments

/-- "hand" — Levin 11.1 Send verbs; alternates DOC/PP, neither argument
    implicit. -/
def hand : Verb := .mkRegular {
  form := "hand"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  vendlerClass := some .accomplishment
  levinClass := some .send }

/-- "lend" — alternates DOC/PP. Neither argument implicit. -/
def lend : Verb where
  form := "lend"
  form3sg := "lends"
  formPast := "lent"
  formPastPart := "lent"
  formPresPart := "lending"
  frames := [ArgumentFrame.np_np, ArgumentFrame.np_pp]
  vendlerClass := some .accomplishment
  levinClass := some .give

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

/-- The past participle in passive voice: the same form as `toWord .pastParticiple`, marked
passive. -/
def Verb.passiveParticiple (v : Verb) : Word :=
  { form := v.formPastPart, cat := .VERB,
    features := Features.of (verbForm := some .Part) (voice := some .Pass) }


end English
