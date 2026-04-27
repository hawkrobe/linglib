import Linglib.Theories.Semantics.Verb.VerbEntry
import Linglib.Core.Lexical.MorphRule

/-! # Verbal Predicate Lexicon Fragment

English verb lexical entries with morphology, argument structure, semantic class,
and links to compositional semantics (CoS, attitudes, causatives).

Semantic types (`ComplementType`, `Attitude`, etc.) and the
cross-linguistic `VerbCore` structure live in `Core/Verbs.lean`. This file
defines `VerbEntry extends VerbCore` with English-specific inflectional fields
and provides smart constructors for regular verbs.
-/

namespace Fragments.English.Predicates.Verbal

-- Re-export Core.Verbs types so downstream files that open this namespace
-- (e.g., `open Fragments.English.Predicates.Verbal (ComplementType ...)`)
-- continue to find them.
export Core.Verbs (Preferential Attitude PresupTriggerType
  ProjectionBehavior ComplementType ControlType VerbCore ImplicitInterp
  complementToValence)

open Core.Verbs
-- Causative, Implicative already in scope via `open Core.Verbs`
open Core.Verbs
open Semantics.Verb.DegreeAchievement (DegreeAchievementScale)
open Core.Scale (Boundedness)
open Semantics.Events.Incrementality (VerbIncClass)
open Semantics.Verb.EntailmentProfile (EntailmentProfile)

-- ════════════════════════════════════════════════════
-- § English Morphophonological Rules
-- ════════════════════════════════════════════════════

private def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

/-- Does the stem end in a consonant followed by 'y'? -/
private def endsWithConsonantY (s : String) : Bool :=
  match s.toList.reverse with
  | 'y' :: c :: _ => !isVowel c
  | _ => false

/-- Does the stem end in a sibilant (sh, ch, ss, x, z)? -/
private def endsWithSibilant (s : String) : Bool :=
  s.endsWith "sh" || s.endsWith "ch" || s.endsWith "ss" ||
  s.endsWith "x" || s.endsWith "z"

/-- Compute regular 3sg present form. -/
def regular3sg (stem : String) : String :=
  if endsWithConsonantY stem then (stem.toList.dropLast ++ "ies".toList) |> String.ofList
  else if endsWithSibilant stem then stem ++ "es"
  else stem ++ "s"

/-- Compute regular past tense / past participle form. -/
def regularPast (stem : String) : String :=
  if endsWithConsonantY stem then (stem.toList.dropLast ++ "ied".toList) |> String.ofList
  else if stem.endsWith "e" then stem ++ "d"
  else stem ++ "ed"

/-- Compute regular present participle form. -/
def regularPresPart (stem : String) : String :=
  if stem.endsWith "e" && !stem.endsWith "ee" then
    (stem.toList.dropLast ++ "ing".toList) |> String.ofList
  else stem ++ "ing"

-- ════════════════════════════════════════════════════
-- § VerbEntry (extends VerbCore with English morphology)
-- ════════════════════════════════════════════════════

/--
A complete English lexical entry for a verb.

Extends the cross-linguistic `VerbCore` (argument structure, semantic class,
compositional links) with English-specific inflectional morphology.
-/
structure VerbEntry extends VerbCore where
  /-- Third person singular present (for agreement) -/
  form3sg : String
  /-- Past tense form -/
  formPast : String
  /-- Past participle (for passives, perfects) -/
  formPastPart : String
  /-- Present participle / gerund -/
  formPresPart : String
  /-- Are all inflected forms rule-predictable from the citation form? -/
  isRegular : Bool := false
  deriving Repr, BEq

/-- Construct a regular verb entry: inflected forms are computed from the
    citation form via English morphophonological rules.

    Usage:
    ```
    def kick : VerbEntry :=.mkRegular {
      form := "kick", complementType :=.np }
    ``` -/
def VerbEntry.mkRegular (core : VerbCore) : VerbEntry :=
  { toVerbCore := core
    form3sg := regular3sg core.form
    formPast := regularPast core.form
    formPastPart := regularPast core.form
    formPresPart := regularPresPart core.form
    isRegular := true }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Simple
-- ════════════════════════════════════════════════════

/-- "sleep" — intransitive, no presupposition -/
def sleep : VerbEntry where
  form := "sleep"
  form3sg := "sleeps"
  formPast := "slept"
  formPastPart := "slept"
  formPresPart := "sleeping"
  complementType := .none
  passivizable := false
  vendlerClass := some .state

/-- "run" — intransitive, no presupposition -/
def run : VerbEntry where
  form := "run"
  form3sg := "runs"
  formPast := "ran"
  formPastPart := "run"
  formPresPart := "running"
  complementType := .none
  subjectEntailments := some ⟨true, true, false, true, true, false, false, false, false, false⟩
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion
  rootProfile := some {
    forceMag := some [.moderate]
    agentVolition := some [.volitional]
    agentControl := some [.compatible]
  }

/-- "arrive" — unaccusative intransitive -/
def arrive : VerbEntry := .mkRegular {
  form := "arrive"
  complementType := .none
  subjectEntailments := some ⟨false, false, false, true, true, true, false, false, false, false⟩
  unaccusative := true
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .inherentlyDirectedMotion }

/-- "eat" — transitive, implicit object is indefinite ("Have you eaten?") -/
def eat : VerbEntry where
  form := "eat"
  form3sg := "eats"
  formPast := "ate"
  formPastPart := "eaten"
  formPresPart := "eating"
  complementType := .np
  subjectEntailments := some ⟨true, true, true, true, true, false, false, false, false, false⟩
  objectEntailments := some ⟨false, false, false, false, false, true, true, true, false, false⟩
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .eat
  rootProfile := some {
    forceMag := some [.low, .moderate]
    agentVolition := some [.volitional]
    agentControl := some [.compatible]
  }

/-- "kick" — transitive -/
def kick : VerbEntry := .mkRegular {
  form := "kick"
  complementType := .np
  subjectEntailments := some ⟨true, true, true, true, true, false, false, false, false, false⟩
  objectEntailments := some ⟨false, false, false, false, false, true, false, true, true, false⟩
  vendlerClass := some .activity
  levinClass := some .hit
  rootProfile := some {
    forceMag := some [.moderate, .high]
    forceDir := some [.unidirectional]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "give" — ditransitive, alternates DOC/PP.
    Implicit goal is definite (@cite{fillmore-1986}: pragmatically recoverable).
    Neither object can be implicit alone. -/
def give : VerbEntry where
  form := "give"
  form3sg := "gives"
  formPast := "gave"
  formPastPart := "given"
  formPresPart := "giving"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment
  levinClass := some .give

/-- "put" — locative -/
def put : VerbEntry where
  form := "put"
  form3sg := "puts"
  formPast := "put"
  formPastPart := "put"
  formPresPart := "putting"
  complementType := .np_pp
  vendlerClass := some .achievement
  levinClass := some .put

/-- "weigh" — measure predicate selecting for mass/weight. -/
def weigh : VerbEntry := .mkRegular {
  form := "weigh"
  complementType := .np
  vendlerClass := some .state
  selectsDimension := some .mass
  levinClass := some .measure }

/-- "cover" — motion/extent predicate selecting for distance. -/
def cover : VerbEntry := .mkRegular {
  form := "cover"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  selectsDimension := some .distance }

/-- "measure" — general measurement predicate. -/
def measure : VerbEntry := .mkRegular {
  form := "measure"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .measure }

/-- "buy" — irregular transitive -/
def buy : VerbEntry where
  form := "buy"
  form3sg := "buys"
  formPast := "bought"
  formPastPart := "bought"
  formPresPart := "buying"
  complementType := .np
  subjectEntailments := some ⟨true, true, true, false, true, false, false, false, false, false⟩
  vendlerClass := some .accomplishment

/-- "meet" — irregular transitive -/
def meet : VerbEntry where
  form := "meet"
  form3sg := "meets"
  formPast := "met"
  formPastPart := "met"
  formPresPart := "meeting"
  complementType := .np
  vendlerClass := some .achievement

/-- "sell" — change of possession, alternates DOC/PP.
    Implicit DO is definite; implicit goal is indefinite. -/
def sell : VerbEntry where
  form := "sell"
  form3sg := "sells"
  formPast := "sold"
  formPastPart := "sold"
  formPresPart := "selling"
  complementType := .np
  altComplementType := some .np_pp
  subjectEntailments := some ⟨true, true, true, false, true, false, false, false, false, false⟩
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .accomplishment

/-- "leave" — transitive (also used intransitively with argument drop) -/
def leave : VerbEntry where
  form := "leave"
  form3sg := "leaves"
  formPast := "left"
  formPastPart := "left"
  formPresPart := "leaving"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .leave

/-- "see" — transitive, can also embed clauses -/
def see : VerbEntry where
  form := "see"
  form3sg := "sees"
  formPast := "saw"
  formPastPart := "seen"
  formPresPart := "seeing"
  complementType := .np
  altComplementType := some .finiteClause
  subjectEntailments := some ⟨false, true, false, false, true, false, false, false, false, false⟩
  vendlerClass := some .state
  attitude := some (.doxastic .veridical)
  levinClass := some .see

-- ════════════════════════════════════════════════════
-- § Verb Entries — Factive / Semifactive
-- ════════════════════════════════════════════════════

/-- "know" — factive, presupposes complement is true -/
def know : VerbEntry where
  form := "know"
  form3sg := "knows"
  formPast := "knew"
  formPastPart := "known"
  formPresPart := "knowing"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  presupType := some .softTrigger
  projectionBehavior := some .hole
  takesQuestionBase := true
  complementSig := some .mono
  attitude := some (.doxastic .veridical)

/-- "regret" — factive, presupposes complement is true -/
def regret : VerbEntry where
  form := "regret"
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  presupType := some .softTrigger
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical)

/-- "realize" — factive, presupposes complement is true -/
def realize : VerbEntry := .mkRegular {
  form := "realize"
  complementType := .finiteClause
  vendlerClass := some .achievement
  passivizable := false
  presupType := some .softTrigger
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical) }

/-- "discover" — semifactive, weaker projection -/
def discover : VerbEntry := .mkRegular {
  form := "discover"
  complementType := .finiteClause
  vendlerClass := some .achievement
  passivizable := false
  presupType := some .softTrigger
  projectionBehavior := some .hole
  takesQuestionBase := true
  attitude := some (.doxastic .veridical) }

/-- "notice" — semifactive -/
def notice : VerbEntry := .mkRegular {
  form := "notice"
  complementType := .finiteClause
  vendlerClass := some .achievement
  passivizable := false
  presupType := some .softTrigger
  projectionBehavior := some .hole
  attitude := some (.doxastic .veridical) }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Change of State
-- ════════════════════════════════════════════════════

/-- "stop" — CoS cessation, presupposes activity was happening -/
def stop : VerbEntry where
  form := "stop"
  form3sg := "stops"
  formPast := "stopped"
  formPastPart := "stopped"
  formPresPart := "stopping"
  complementType := .gerund
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
  projectionBehavior := some .hole
  cosType := some .cessation
  levinClass := some .aspectual

/-- "quit" — CoS cessation -/
def quit : VerbEntry where
  form := "quit"
  form3sg := "quits"
  formPast := "quit"
  formPastPart := "quit"
  formPresPart := "quitting"
  complementType := .gerund
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
  cosType := some .cessation
  levinClass := some .aspectual

/-- "start" — CoS inception, presupposes activity wasn't happening -/
def start : VerbEntry := .mkRegular {
  form := "start"
  complementType := .gerund
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
  cosType := some .inception
  levinClass := some .aspectual }

/-- "begin" — CoS inception -/
def begin_ : VerbEntry where
  form := "begin"
  form3sg := "begins"
  formPast := "began"
  formPastPart := "begun"
  formPresPart := "beginning"
  complementType := .gerund
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
  cosType := some .inception
  levinClass := some .aspectual

/-- "continue" — CoS continuation, presupposes activity was happening -/
def continue_ : VerbEntry := .mkRegular {
  form := "continue"
  complementType := .gerund
  vendlerClass := some .activity
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
  cosType := some .continuation
  levinClass := some .aspectual }

/-- "keep" — CoS continuation -/
def keep : VerbEntry where
  form := "keep"
  form3sg := "keeps"
  formPast := "kept"
  formPastPart := "kept"
  formPresPart := "keeping"
  complementType := .gerund
  vendlerClass := some .activity
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
  cosType := some .continuation
  levinClass := some .aspectual

-- ════════════════════════════════════════════════════
-- § Verb Entries — Implicative / Control
-- ════════════════════════════════════════════════════

/-- "manage" — positive implicative: "managed to VP" entails "VP".
    Traditional analysis: agentive subject controls the complement.
    See also `manage_occasion` for the @cite{solstad-bott-2024} analysis. -/
def manage : VerbEntry := .mkRegular {
  form := "manage"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  projectionBehavior := some .hole
  presupType := some .prerequisiteSoft
  implicative := some .positive }

/-- "fail" — negative implicative: "failed to VP" entails "not VP" -/
def fail : VerbEntry := .mkRegular {
  form := "fail"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .negative }

/-- "try" — subject control, no entailment -/
def try_ : VerbEntry where
  form := "try"
  form3sg := "tries"
  formPast := "tried"
  formPastPart := "tried"
  formPresPart := "trying"
  complementType := .infinitival
  vendlerClass := some .activity
  controlType := .subjectControl
  passivizable := false

/-- "persuade" — object control: "persuade X to VP" (X = agent of VP).
    Psychological attitude verb: causes the object to form an intention.
    Projects AUTHOR coordinate → obligatory *de se* (@cite{landau-2015} table (36)). -/
def persuade : VerbEntry := .mkRegular {
  form := "persuade"
  complementType := .infinitival
  vendlerClass := some .accomplishment
  controlType := .objectControl
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "promise" — subject control with object: "promise X to VP".
    Desiderative attitude verb: the subject commits to a future action.
    @cite{landau-2015} (5c) classifies it as desiderative → logophoric control. -/
def promise : VerbEntry := .mkRegular {
  form := "promise"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  projectionBehavior := some .plug
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive)) }

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : VerbEntry := .mkRegular {
  form := "remember"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .positive }

/-- "forget" — negative implicative with infinitival -/
def forget : VerbEntry where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .negative

/-- "neglect" — negative implicative (@cite{karttunen-1971} §10, ex. 38):
    "John neglected to lock his door" entails "John didn't lock his door." -/
def neglect : VerbEntry := .mkRegular {
  form := "neglect"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .negative }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Doxastic Attitude
-- ════════════════════════════════════════════════════

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : VerbEntry := .mkRegular {
  form := "believe"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  projectionBehavior := some .hole
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono }

/-- "think" — doxastic attitude verb -/
def think : VerbEntry where
  form := "think"
  form3sg := "thinks"
  formPast := "thought"
  formPastPart := "thought"
  formPresPart := "thinking"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono

-- ════════════════════════════════════════════════════
-- § Verb Entries — Preferential Attitude
-- ════════════════════════════════════════════════════

/-- "want" — preferential attitude verb with infinitival complement -/
def want : VerbEntry := .mkRegular {
  form := "want"
  complementType := .infinitival
  vendlerClass := some .state
  controlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono
  levinClass := some .want }

/-- "intend" — intention-reporting attitude verb (@cite{grano-2024}).
    Primary frame: infinitival with subject control ("intend to leave").
    Alternate frame: for-to non-control ("intend for Ben to come along").
    Rejects indicative complements cross-linguistically: *"Kim intends
    that Sandy leaves." Requires eventuality abstraction (CAUSE* binds
    the complement's event argument). -/
def intend : VerbEntry := .mkRegular {
  form := "intend"
  complementType := .infinitival
  vendlerClass := some .state
  controlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want }

/-- "decide" — belief/intention hybrid attitude verb (@cite{grano-2024}, §6.2).
    Nonfinite complement → intention formation: "Kim decided to quit smoking"
    Finite complement → belief formation: "Kim decided that smoking is harmful"
    The complement type determines the reading, as with Italian *convincere*
    (@cite{fusco-sgrizzi-2026}). -/
def decide_ : VerbEntry := .mkRegular {
  form := "decide"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  altComplementType := some .finiteClause
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  levinClass := some .want }

/-- "hope" — preferential attitude verb (Class 3: anti-rogative).
    Primary frame: finite clause ("hope that John leaves").
    Alternate frame: infinitival with subject control ("hope to leave"). -/
def hope : VerbEntry := .mkRegular {
  form := "hope"
  complementType := .finiteClause
  vendlerClass := some .state
  altComplementType := some .infinitival
  altControlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono }

/-- "pray" — preferential attitude verb, permits future temporal orientation.
    @cite{klecha-2016}: like *hope*, *pray* can take a circumstantial modal base,
    allowing future-oriented readings under past tense morphology.
    Primary frame: finite clause ("pray that God helps").
    Alternate frame: infinitival with subject control ("pray to be saved"). -/
def pray : VerbEntry := .mkRegular {
  form := "pray"
  complementType := .finiteClause
  vendlerClass := some .state
  altComplementType := some .infinitival
  altControlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono }

/-- "expect" — preferential attitude verb (Class 3: anti-rogative) -/
def expect : VerbEntry := .mkRegular {
  form := "expect"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono }

/-- "wish" — preferential attitude verb (Class 3: anti-rogative) -/
def wish : VerbEntry where
  form := "wish"
  form3sg := "wishes"
  formPast := "wished"
  formPastPart := "wished"
  formPresPart := "wishing"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono
  levinClass := some .want

/-- "fear" — preferential attitude verb (Class 2: takes questions) -/
def fear : VerbEntry := .mkRegular {
  form := "fear"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  complementSig := some .mono
  levinClass := some .admire }

/-- "dread" — preferential attitude verb (Class 2: takes questions) -/
def dread : VerbEntry := .mkRegular {
  form := "dread"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))
  complementSig := some .mono
  levinClass := some .admire }

/-- "worry" — preferential attitude verb (Class 1: takes questions, non-C-distributive) -/
def worry : VerbEntry where
  form := "worry"
  form3sg := "worries"
  formPast := "worried"
  formPastPart := "worried"
  formPresPart := "worrying"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased)
  complementSig := some .mono

-- ════════════════════════════════════════════════════
-- § Verb Entries — Raising
-- ════════════════════════════════════════════════════

/-- "seem" — raising verb (no theta role for subject, unaccusative) -/
def seem : VerbEntry := .mkRegular {
  form := "seem"
  complementType := .infinitival
  vendlerClass := some .state
  controlType := .raising
  passivizable := false
  unaccusative := true }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Causative (Periphrastic)
-- ════════════════════════════════════════════════════

/-- "cause" — counterfactual dependence (necessity semantics) -/
def cause : VerbEntry := .mkRegular {
  form := "cause"
  complementType := .infinitival
  vendlerClass := some .accomplishment
  controlType := .objectControl
  causative := some .cause
  levinClass := some .engender }

/-- "make" — direct sufficient guarantee -/
def make : VerbEntry where
  form := "make"
  form3sg := "makes"
  formPast := "made"
  formPastPart := "made"
  formPresPart := "making"
  complementType := .smallClause
  vendlerClass := some .accomplishment
  controlType := .objectControl
  causative := some .make

/-- "let" — permissive causative (barrier removal) -/
def let_ : VerbEntry where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  complementType := .smallClause
  vendlerClass := some .achievement
  controlType := .objectControl
  causative := some .enable

/-- "have" — causative use (directive causation) -/
def have_caus : VerbEntry where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  complementType := .smallClause
  vendlerClass := some .achievement
  controlType := .objectControl
  causative := some .make
  senseTag := .causative

/-- "get" — causative use (persuasive causation) -/
def get_caus : VerbEntry where
  form := "get"
  form3sg := "gets"
  formPast := "got"
  formPastPart := "gotten"
  formPresPart := "getting"
  complementType := .infinitival
  vendlerClass := some .accomplishment
  controlType := .objectControl
  causative := some .make
  senseTag := .causative

/-- "force" — coercive causative (overcome resistance) -/
def force : VerbEntry := .mkRegular {
  form := "force"
  complementType := .infinitival
  vendlerClass := some .accomplishment
  controlType := .objectControl
  projectionBehavior := some .hole
  causative := some .force }

/-- "prevent" — blocking causative (barrier addition).
    "X prevented Y from V-ing" entails the effect did NOT occur
    (¬p in w₀) but would have without X's intervention.
    @cite{nadathur-lauer-2020}: `preventSem` (dual of `causeSem`). -/
def prevent : VerbEntry := .mkRegular {
  form := "prevent"
  complementType := .gerund
  vendlerClass := some .accomplishment
  controlType := .objectControl
  projectionBehavior := some .hole
  causative := some .prevent }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Lexical Causatives
-- ════════════════════════════════════════════════════

/-- "kill" — thin lexical causative (kill = cause-to-die, COMPACT type). -/
def kill : VerbEntry := .mkRegular {
  form := "kill"
  complementType := .np
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .murder
  rootProfile := some {
    resultType := some [.totalDestruction]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "break" — thick lexical causative (Levin 45.1 Break Verbs; @cite{embick-2009} break-class).
    Pure change-of-state verb: change in "material integrity"
    with no specification of how the change comes about (@cite{levin-1993}:242). -/
def break_ : VerbEntry where
  form := "break"
  form3sg := "breaks"
  formPast := "broke"
  formPastPart := "broken"
  formPresPart := "breaking"
  complementType := .np
  unaccusative := false
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .break_
  rootProfile := some {
    forceMag := some [.moderate, .high]
    -- forceDir unconstrained: *break* covers snapping (bidirectional),
    -- hammering (omnidirectional), and directed blows (unidirectional)
    patientRob := some [.moderate, .robust]
    resultType := some [.fracture]
    agentControl := some [.incompatible, .neutral]
    -- break is unspecified for instrument and object dimensionality
    -- (@cite{majid-boster-bowerman-2008}: Dim 1 low predictability)
  }

/-- "tear" — Levin 45.1 Break Verbs. Contrary-direction separation with force.
    Unlike *break*, *tear* implies a specific directionality (bidirectional /
    pulling apart) and is compatible with careful controlled action.
    Patient restriction: any solid capable of irregular separation.
    @cite{spalek-mcnally-2026} (§3.1–3.2).
    @cite{majid-boster-bowerman-2008}: Dimension 2 — tearing consistently
    distinguished from break/cut across 10/28 languages. -/
def tear_ : VerbEntry where
  form := "tear"
  form3sg := "tears"
  formPast := "tore"
  formPastPart := "torn"
  formPresPart := "tearing"
  complementType := .np
  unaccusative := false
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causative := some .make
  levinClass := some .break_
  rootProfile := some {
    forceMag := some [.moderate, .high]
    forceDir := some [.bidirectional, .unidirectional]
    patientRob := some [.flimsy, .moderate, .robust]
    resultType := some [.separation]
    agentControl := some [.neutral, .compatible]
    instrumentType := some [.hands]
    patientDim := some [.twoD]
  }

-- ════════════════════════════════════════════════════
-- § Physical Disturbance CoS Verbs (@cite{tham-2025})
-- ════════════════════════════════════════════════════

/-- "crack" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    @cite{tham-2025}: closed scale (contra @cite{rappaport-hovav-2014} two-point
    classification), but allows BOTH telic ("cracked in a minute") and atelic
    ("cracked for two days") readings. Compatible with *completely*, *partially*,
    *badly*. The verb is NOT a standard degree achievement: its variable telicity
    does not reduce to scale boundedness alone. -/
def crack : VerbEntry := .mkRegular {
  form := "crack"
  complementType := .np
  unaccusative := true
  vendlerClass := some .achievement
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "cracking",
    baseAdjective := some "cracked" }
  causative := some .make
  levinClass := some .break_ }

/-- "dent" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    @cite{tham-2025}: closed scale, compatible with *more dented*, *completely
    dented*, *badly dented*. -/
def dent : VerbEntry := .mkRegular {
  form := "dent"
  complementType := .np
  unaccusative := true
  vendlerClass := some .achievement
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "denting",
    baseAdjective := some "dented" }
  causative := some .make
  levinClass := some .break_ }

/-- "scratch" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    @cite{tham-2025}: closed scale, compatible with *more scratched*, *completely
    scratched*, *badly scratched*. Note: also has a manner reading (Levin
    §10.4.1 wipe verbs: "The cat scratched the sofa") distinct from
    the CoS reading formalized here. -/
def scratch : VerbEntry := .mkRegular {
  form := "scratch"
  complementType := .np
  unaccusative := true
  vendlerClass := some .achievement
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "scratching",
    baseAdjective := some "scratched" }
  causative := some .make
  levinClass := some .break_ }

/-- "shatter" — Levin 45.1 Break verbs. NOT a physical disturbance verb.
    Punctual, non-gradable: *shatter in two minutes* (after, not duration),
    #*shatter for two minutes*, ??*more shattered* (@cite{tham-2025} (12)). -/
def shatter : VerbEntry := .mkRegular {
  form := "shatter"
  complementType := .np
  unaccusative := true
  vendlerClass := some .achievement
  causative := some .make
  levinClass := some .break_ }

/-- "burn" — thick lexical causative (manner = by fire/heat). -/
def burn : VerbEntry := .mkRegular {
  form := "burn"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causative := some .make
  levinClass := some .otherCoS
  rootProfile := some {
    forceMag := some [.moderate, .high]
    patientRob := some [.flimsy, .moderate, .robust]
    resultType := some [.totalDestruction, .deformation]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "destroy" — thin lexical causative (result-only, no manner). -/
def destroy : VerbEntry := .mkRegular {
  form := "destroy"
  complementType := .np
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .destroy
  rootProfile := some {
    resultType := some [.totalDestruction]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "melt" — thick lexical causative (manner = by heat).
    Base transitive that productively takes DOC ("melt me some ice cream").
    Implicit obj is indefinite ("the ice cream melted" / "we're melting"). -/
def melt : VerbEntry := .mkRegular {
  form := "melt"
  complementType := .np
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causative := some .make
  levinClass := some .otherCoS
  rootProfile := some {
    forceMag := some [.low, .moderate]
    patientRob := some [.moderate, .robust]
    resultType := some [.deformation]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.compatible]
  } }

-- ════════════════════════════════════════════════════
-- § @cite{martin-rose-nichols-2025} — Thick/Thin Causatives
-- ════════════════════════════════════════════════════

-- Entries for causative verbs classified by @cite{martin-rose-nichols-2025} that don't
-- already have Fragment entries elsewhere (break_, burn, destroy, melt, kill,
-- cut, mix, start, stop already defined above).

/-- "activate" — thin causative, CoS without manner. -/
def activate : VerbEntry := .mkRegular {
  form := "activate"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

/-- "affect" — thin causative, general effect. -/
def affect : VerbEntry := .mkRegular {
  form := "affect"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .destroy }

/-- "change" — thin causative, transformation (§26.6). -/
def change : VerbEntry := .mkRegular {
  form := "change"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .turn }

/-- "damage" — thin causative, partial destruction. -/
def damage : VerbEntry := .mkRegular {
  form := "damage"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .destroy }

/-- "eliminate" — thin causative, removal/destruction. -/
def eliminate : VerbEntry := .mkRegular {
  form := "eliminate"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .destroy }

/-- "hurt" — thin causative, generic harm. -/
def hurt : VerbEntry where
  form := "hurt"
  form3sg := "hurts"
  formPast := "hurt"
  formPastPart := "hurt"
  formPresPart := "hurting"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .destroy

/-- "restore" — thin causative, reverse transformation (§26.6). -/
def restore : VerbEntry := .mkRegular {
  form := "restore"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .turn }

/-- "trigger" — thin causative, engender class (§27). -/
def trigger : VerbEntry := .mkRegular {
  form := "trigger"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .engender }

/-- "bury" — thick causative (state), concealment (§16). -/
def bury : VerbEntry := .mkRegular {
  form := "bury"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .conceal }

/-- "drop" — thick causative, caused falling (§45.4). -/
def drop : VerbEntry := .mkRegular {
  form := "drop"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

/-- "lift" — thick causative, caused upward motion (§11.4 carry). -/
def lift : VerbEntry := .mkRegular {
  form := "lift"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .carry }

/-- "lock" — thick causative, caused secured state (§45.4). -/
def lock : VerbEntry := .mkRegular {
  form := "lock"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

/-- "shut" — thick causative, caused closed state (§45.4). -/
def shut : VerbEntry where
  form := "shut"
  form3sg := "shuts"
  formPast := "shut"
  formPastPart := "shut"
  formPresPart := "shutting"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS

/-- "spread" — thick causative, spray/load class (§9.7). -/
def spread : VerbEntry where
  form := "spread"
  form3sg := "spreads"
  formPast := "spread"
  formPastPart := "spread"
  formPresPart := "spreading"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .sprayLoad

/-- "stretch" — thick causative, bend class (§45.2). -/
def stretch : VerbEntry := .mkRegular {
  form := "stretch"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .bend }

/-- "switch" — thick causative, CoS (§45.4). -/
def switch : VerbEntry := .mkRegular {
  form := "switch"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Other
-- ════════════════════════════════════════════════════

/-- "devour" — transitive, no presupposition -/
def devour : VerbEntry := .mkRegular {
  form := "devour"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .devour
  rootProfile := some {
    forceMag := some [.moderate, .high]
    agentVolition := some [.volitional]
    agentControl := some [.neutral]
  } }

/-- "read" — transitive, no presupposition -/
def read : VerbEntry where
  form := "read"
  form3sg := "reads"
  formPast := "read"
  formPastPart := "read"
  formPresPart := "reading"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .inc

/-- "build" — creation verb, strictly incremental theme.
    Base transitive that productively takes DOC ("build us a house"). -/
def build : VerbEntry where
  form := "build"
  form3sg := "builds"
  formPast := "built"
  formPastPart := "built"
  formPresPart := "building"
  complementType := .np
  subjectEntailments := some ⟨true, true, true, true, true, false, false, false, false, false⟩
  objectEntailments := some ⟨false, false, false, false, false, true, true, true, false, true⟩
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .build

/-- "write" — creation verb, strictly incremental theme.
    Alternates DOC/PP. Implicit DO in both frames (indefinite).
    Uniquely allows implicit DO in both DOC and PP (@cite{bruening-2021}). -/
def write : VerbEntry where
  form := "write"
  form3sg := "writes"
  formPast := "wrote"
  formPastPart := "written"
  formPresPart := "writing"
  complementType := .np
  altComplementType := some .np_pp
  implicitObj := some .indef
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .build

/-- "sweep" — motion + sustained contact, variable agentivity (default sense). -/
def sweep : VerbEntry where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  complementType := .np
  vendlerClass := some .activity
  subjectEntailments := some ⟨false, false, false, true, true, false, false, false, false, false⟩
  passivizable := true
  levinClass := some .wipe
  rootProfile := some {
    forceMag := some [.low, .moderate]
    forceDir := some [.unidirectional]
    agentVolition := some [.volitional]
    agentControl := some [.compatible]
  }

/-- "sweep" instrument sense — obligatorily agentive, broom lexicalized. -/
def sweep_instr : VerbEntry where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  complementType := .np
  vendlerClass := some .activity
  subjectEntailments := some ⟨true, true, true, true, true, false, false, false, false, false⟩
  passivizable := true
  senseTag := .instrumental
  levinClass := some .wipe
  rootProfile := some {
    forceMag := some [.low, .moderate]
    forceDir := some [.unidirectional]
    agentVolition := some [.volitional]
    agentControl := some [.compatible]
  }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Communication
-- ════════════════════════════════════════════════════

/-- "say" — communication verb, not factive -/
def say : VerbEntry where
  form := "say"
  form3sg := "says"
  formPast := "said"
  formPastPart := "said"
  formPresPart := "saying"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClass := some .say

/-- "tell" — communication verb with recipient.
    Also ditransitive ("tell me a story"). Implicit second obj is definite
    (@cite{bruening-2021}: recoverable). Implicit goal (PP) is indefinite. -/
def tell : VerbEntry where
  form := "tell"
  form3sg := "tells"
  formPast := "told"
  formPastPart := "told"
  formPresPart := "telling"
  speechActVerb := true
  complementType := .finiteClause
  altComplementType := some .np_np
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClass := some .tell

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : VerbEntry := .mkRegular {
  form := "claim"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .achievement
  projectionBehavior := some .plug
  levinClass := some .say }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Clause-Embedding Predicates (@cite{degen-tonhauser-2021})
-- ════════════════════════════════════════════════════

/-! The 20 clause-embedding predicates from @cite{degen-tonhauser-2021}.
    Predicates already defined above: know, discover, see, think, say, hear.
    "be annoyed" and "be right" are copular constructions, not simple verbs. -/

/-- "reveal" — factive communication verb (@cite{degen-tonhauser-2022}: canonically factive) -/
def reveal : VerbEntry := .mkRegular {
  form := "reveal"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  presupType := some .softTrigger
  attitude := some (.doxastic .veridical)
  levinClass := some .say }

/-- "acknowledge" — optionally factive communication verb -/
def acknowledge : VerbEntry := .mkRegular {
  form := "acknowledge"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say }

/-- "admit" — optionally factive communication verb -/
def admit : VerbEntry where
  form := "admit"
  form3sg := "admits"
  formPast := "admitted"
  formPastPart := "admitted"
  formPresPart := "admitting"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say

/-- "announce" — communication verb -/
def announce : VerbEntry := .mkRegular {
  form := "announce"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say }

/-- "confess" — optionally factive communication verb -/
def confess : VerbEntry := .mkRegular {
  form := "confess"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say }

/-- "inform" — optionally factive communication verb with recipient -/
def inform : VerbEntry := .mkRegular {
  form := "inform"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .tell }

/-- "suggest" — non-factive communication verb -/
def suggest : VerbEntry := .mkRegular {
  form := "suggest"
  complementType := .finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClass := some .say }

/-- "pretend" — anti-veridical attitude verb -/
def pretend : VerbEntry := .mkRegular {
  form := "pretend"
  complementType := .finiteClause
  vendlerClass := some .activity
  opaqueContext := true }

/-- "confirm" — evidential verb -/
def confirm : VerbEntry := .mkRegular {
  form := "confirm"
  complementType := .finiteClause
  vendlerClass := some .achievement }

/-- "demonstrate" — evidential verb -/
def demonstrate : VerbEntry := .mkRegular {
  form := "demonstrate"
  complementType := .finiteClause
  vendlerClass := some .achievement }

/-- "establish" — evidential verb -/
def establish : VerbEntry := .mkRegular {
  form := "establish"
  complementType := .finiteClause
  vendlerClass := some .achievement }

/-- "prove" — evidential verb -/
def prove : VerbEntry := .mkRegular {
  form := "prove"
  complementType := .finiteClause
  vendlerClass := some .achievement }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Manner of Speaking (Levin 37.3)
-- ════════════════════════════════════════════════════

/-! Manner-of-speaking (MoS) verbs specify *how* something is said.
    @cite{storment-2026} shows these divide into two classes:
    - **QI-permitting** (unaccusative): whisper, murmur, mumble, mutter, shout,
      cry, scream, shriek, yell, groan, grumble, hiss, sigh, whimper, snap
    - **Non-QI** (unergative): speak, talk -/

/-- "whisper" — MoS verb, permits quotative inversion (unaccusative) -/
def whisper : VerbEntry := .mkRegular {
  form := "whisper"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "murmur" — MoS verb, permits quotative inversion (unaccusative) -/
def murmur : VerbEntry := .mkRegular {
  form := "murmur"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "shout" — MoS verb, permits quotative inversion (unaccusative) -/
def shout : VerbEntry := .mkRegular {
  form := "shout"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "cry" — MoS verb, permits quotative inversion (unaccusative) -/
def cry : VerbEntry := .mkRegular {
  form := "cry"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "scream" — MoS verb, permits quotative inversion (unaccusative) -/
def scream : VerbEntry := .mkRegular {
  form := "scream"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "mumble" — MoS verb, permits quotative inversion (unaccusative) -/
def mumble : VerbEntry := .mkRegular {
  form := "mumble"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "mutter" — MoS verb, permits quotative inversion (unaccusative) -/
def mutter : VerbEntry := .mkRegular {
  form := "mutter"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "shriek" — MoS verb, permits quotative inversion (unaccusative) -/
def shriek : VerbEntry := .mkRegular {
  form := "shriek"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "yell" — MoS verb, permits quotative inversion (unaccusative) -/
def yell : VerbEntry := .mkRegular {
  form := "yell"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "groan" — MoS verb, permits quotative inversion (unaccusative) -/
def groan : VerbEntry := .mkRegular {
  form := "groan"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "grumble" — MoS verb, permits quotative inversion (unaccusative) -/
def grumble : VerbEntry := .mkRegular {
  form := "grumble"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "hiss" — MoS verb, permits quotative inversion (unaccusative) -/
def hiss : VerbEntry := .mkRegular {
  form := "hiss"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "sigh" — MoS verb, permits quotative inversion (unaccusative) -/
def sigh : VerbEntry := .mkRegular {
  form := "sigh"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "whimper" — MoS verb, permits quotative inversion (unaccusative) -/
def whimper : VerbEntry := .mkRegular {
  form := "whimper"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "snap" — MoS verb, permits quotative inversion (unaccusative) -/
def snap : VerbEntry := .mkRegular {
  form := "snap"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "speak" — agentive communication verb, blocks quotative inversion (unergative) -/
def speak : VerbEntry where
  form := "speak"
  form3sg := "speaks"
  formPast := "spoke"
  formPastPart := "spoken"
  formPresPart := "speaking"
  speechActVerb := true
  complementType := .none
  vendlerClass := some .activity
  passivizable := false
  levinClass := some .mannerOfSpeaking

/-- "talk" — agentive communication verb, blocks quotative inversion (unergative) -/
def talk : VerbEntry := .mkRegular {
  form := "talk"
  speechActVerb := true
  complementType := .none
  vendlerClass := some .activity
  passivizable := false
  levinClass := some .mannerOfSpeaking }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Question-Embedding
-- ════════════════════════════════════════════════════

/-- "wonder" — embeds questions only -/
def wonder : VerbEntry := .mkRegular {
  form := "wonder"
  complementType := .question
  vendlerClass := some .state
  takesQuestionBase := true
  opaqueContext := true }

/-- "ask" — embeds questions -/
def ask : VerbEntry := .mkRegular {
  form := "ask"
  speechActVerb := true
  complementType := .question
  vendlerClass := some .achievement
  takesQuestionBase := true }

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : VerbEntry := .mkRegular {
  form := "investigate"
  complementType := .question
  vendlerClass := some .activity
  takesQuestionBase := true
  levinClass := some .search }

/-- "depend_on" — rogative, embeds interrogatives only (@cite{dayal-2025}: rogativeCP) -/
def depend_on : VerbEntry where
  form := "depend on"
  form3sg := "depends on"
  formPast := "depended on"
  formPastPart := "depended on"
  formPresPart := "depending on"
  complementType := .question
  vendlerClass := some .state
  takesQuestionBase := true

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : VerbEntry := .mkRegular {
  form := "remember"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  presupType := some .softTrigger
  attitude := some (.doxastic .veridical)
  takesQuestionBase := true
  senseTag := .rogative }

/-- "forget" in factive/question-embedding sense. -/
def forget_rog : VerbEntry where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  complementType := .finiteClause
  vendlerClass := some .state
  passivizable := false
  presupType := some .softTrigger
  attitude := some (.doxastic .veridical)
  takesQuestionBase := true
  senseTag := .rogative

-- ════════════════════════════════════════════════════
-- § Verb Entries — Occasion Verbs (@cite{solstad-bott-2024})
-- ════════════════════════════════════════════════════

/-! Occasion verbs presuppose a prior occasioning eventuality and have
    experiencer (agent-evocator) subjects. They pattern with AgExp verbs
    for implicit causality bias.

    "manage" has two entries: `manage` (`.default`, agentive subject — traditional
    implicative analysis) and `manage_occasion` (`.occasion`, experiencer subject —
    Solstad & Bott's agent-evocator analysis). This mirrors @cite{kim-2024}'s observation
    that the same verb can project different effective argument structures
    depending on the interpretive context. -/

/-- "manage" occasion sense — agent-evocator subject.
    Same implicative semantics as `manage`, but subject is experiencer
    (sentience + independent existence, no entailed volition/causation).
    The do-test passes pragmatically because the complement denotes a
    volitional action, not because the matrix verb entails agentivity. -/
def manage_occasion : VerbEntry := .mkRegular {
  form := "manage"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .positive
  presupType := some .prerequisiteSoft
  senseTag := .occasion }

/-- "dare" — positive implicative with prerequisite presupposition: courage.
    "Ana dared to enter the cave" → "Ana entered the cave."
    Presupposes that daring/courageous action was required for complement
    realization (@cite{nadathur-2024} §5.2, ex. 3–4, 26). -/
def dare : VerbEntry := .mkRegular {
  form := "dare"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  presupType := some .prerequisiteSoft
  implicative := some .positive }

/-- "bother" — positive implicative with prerequisite presupposition: engagement.
    "He bothered to answer" → "He answered."
    Presupposes that overcoming apathy/effort was required
    (@cite{nadathur-2024} §2, ex. 10, 28). -/
def bother : VerbEntry := .mkRegular {
  form := "bother"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  presupType := some .prerequisiteSoft
  implicative := some .positive }

/-- "hesitate" — polarity-reversing one-way implicative.
    "Amira hesitated to drink a beer" ↛ "Amira did not drink a beer."
    "Amira did not hesitate to drink a beer" → "Amira drank a beer."
    The paper does not explicitly name the prerequisite for *hesitate*;
    it is treated as a polarity-reversing analog of *dare*
    (@cite{nadathur-2024} §6.4, ex. 45–47). -/
def hesitate : VerbEntry := .mkRegular {
  form := "hesitate"
  complementType := .infinitival
  vendlerClass := some .activity
  controlType := .subjectControl
  passivizable := false
  presupType := some .prerequisiteSoft
  implicative := some .negative }

/-- "venture" — positive implicative (@cite{karttunen-1971} ex. 2):
    "John ventured to speak" entails "John spoke." -/
def venture : VerbEntry := .mkRegular {
  form := "venture"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .positive }

/-- "condescend" — positive implicative (@cite{karttunen-1971} ex. 2):
    "John condescended to help" entails "John helped." -/
def condescend : VerbEntry := .mkRegular {
  form := "condescend"
  complementType := .infinitival
  vendlerClass := some .achievement
  controlType := .subjectControl
  passivizable := false
  implicative := some .positive }

/-- "happen" — raising verb, positive implicative (@cite{karttunen-1971} ex. 2):
    "John happened to see Mary" entails "John saw Mary."
    Raising: "It happened to rain" — no theta role for matrix subject. -/
def happen : VerbEntry := .mkRegular {
  form := "happen"
  complementType := .infinitival
  controlType := .raising
  passivizable := false
  implicative := some .positive }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Agent-Experiencer (@cite{solstad-bott-2024})
-- ════════════════════════════════════════════════════

/-! @cite{levin-1993} class 31.2 (admire). Subject = experiencer, object = stimulus.
    NP1 (subject) IC bias. -/

/-- "enjoy" — AgExp verb (experiencer-subject) -/
def enjoy : VerbEntry := .mkRegular {
  form := "enjoy"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "like" — AgExp verb (experiencer-subject) -/
def like : VerbEntry := .mkRegular {
  form := "like"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "love" — AgExp verb (experiencer-subject) -/
def love : VerbEntry := .mkRegular {
  form := "love"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : VerbEntry := .mkRegular {
  form := "hate"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : VerbEntry := .mkRegular {
  form := "admire"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "envy" — AgExp verb (experiencer-subject).
    DOC-only ditransitive ("He envies me the car"). Implicit goal is
    definite (familiar). Implicit second obj is indefinite. -/
def envy : VerbEntry := .mkRegular {
  form := "envy"
  complementType := .np
  altComplementType := some .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .state
  levinClass := some .admire }

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : VerbEntry := .mkRegular {
  form := "respect"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "value" — AgExp verb (experiencer-subject) -/
def value : VerbEntry := .mkRegular {
  form := "value"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : VerbEntry := .mkRegular {
  form := "fear"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : VerbEntry := .mkRegular {
  form := "dread"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .admire }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Stimulus-Experiencer (@cite{solstad-bott-2024})
-- ════════════════════════════════════════════════════

/-! @cite{levin-1993} class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def frighten : VerbEntry := .mkRegular {
  form := "frighten"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "amuse" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def amuse : VerbEntry := .mkRegular {
  form := "amuse"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "fascinate" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def fascinate : VerbEntry := .mkRegular {
  form := "fascinate"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "irritate" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def irritate : VerbEntry := .mkRegular {
  form := "irritate"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "annoy" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def annoy : VerbEntry := .mkRegular {
  form := "annoy"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "bore" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def bore : VerbEntry := .mkRegular {
  form := "bore"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "charm" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def charm : VerbEntry := .mkRegular {
  form := "charm"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "impress" — StimExp verb (stimulus-subject, eventive: @cite{kim-2024} UPH) -/
def impress : VerbEntry := .mkRegular {
  form := "impress"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "concern" — stative Class II psych verb (@cite{kim-2024} UPH, internal cause) -/
def concern : VerbEntry := .mkRegular {
  form := "concern"
  complementType := .np
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "interest" — stative Class II psych verb (@cite{kim-2024} UPH, internal cause) -/
def interest : VerbEntry := .mkRegular {
  form := "interest"
  complementType := .np
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : VerbEntry := .mkRegular {
  form := "surprise"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : VerbEntry := .mkRegular {
  form := "scare"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : VerbEntry := .mkRegular {
  form := "delight"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : VerbEntry := .mkRegular {
  form := "embarrass"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : VerbEntry := .mkRegular {
  form := "upset"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : VerbEntry := .mkRegular {
  form := "disgust"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : VerbEntry := .mkRegular {
  form := "shock"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : VerbEntry := .mkRegular {
  form := "confuse"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : VerbEntry := .mkRegular {
  form := "disappoint"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "worry" (eventive) — Class II, external cause. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : VerbEntry := .mkRegular {
  form := "worry"
  complementType := .np
  vendlerClass := some .accomplishment
  causalSource := some .external
  levinClass := some .amuse }

/-- "worry" (stative) — Class II, internal cause. "The situation worries John."
    @cite{kim-2024} UPH: same theta grid as worry_eventive, different causal source. -/
def worry_stative : VerbEntry := .mkRegular {
  form := "worry"
  complementType := .np
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "please" — stative Class II (@cite{kim-2024} UPH, internal cause).
    "The idea pleases John." Related to B&R Class III It. *piacere*. -/
def please_psych : VerbEntry := .mkRegular {
  form := "please"
  complementType := .np
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "trouble" — stative Class II (@cite{kim-2024} UPH, internal cause).
    "The thought troubles John." -/
def trouble : VerbEntry := .mkRegular {
  form := "trouble"
  complementType := .np
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "puzzle" — stative Class II (@cite{kim-2024} UPH, internal cause).
    "The problem puzzles John." -/
def puzzle : VerbEntry := .mkRegular {
  form := "puzzle"
  complementType := .np
  vendlerClass := some .state
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Agent-Patient (@cite{solstad-bott-2024})
-- ════════════════════════════════════════════════════

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : VerbEntry := .mkRegular {
  form := "chase"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .chase }

/-- "hit" — AgPat verb (Levin 18.1) -/
def hit : VerbEntry where
  form := "hit"
  form3sg := "hits"
  formPast := "hit"
  formPastPart := "hit"
  formPresPart := "hitting"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit

/-- "push" — AgPat verb (Levin 12) -/
def push : VerbEntry := .mkRegular {
  form := "push"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pushPull }

/-- "pull" — AgPat verb (Levin 12) -/
def pull : VerbEntry := .mkRegular {
  form := "pull"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pushPull }

/-- "shove" — verb of exerting force (Levin 12, @cite{levin-2026} (31)) -/
def shove : VerbEntry := .mkRegular {
  form := "shove"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "tug" — verb of exerting force (Levin 12, @cite{levin-2026} (31)) -/
def tug : VerbEntry where
  form := "tug"
  form3sg := "tugs"
  formPast := "tugged"
  formPastPart := "tugged"
  formPresPart := "tugging"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .pushPull

/-- "yank" — verb of exerting force (Levin 12, @cite{levin-2026} (31)) -/
def yank : VerbEntry := .mkRegular {
  form := "yank"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "jerk" — verb of exerting force (Levin 12, @cite{levin-2026} (31)) -/
def jerk : VerbEntry := .mkRegular {
  form := "jerk"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "wrench" — verb of exerting force (Levin 12, @cite{levin-2026} (31)) -/
def wrench : VerbEntry := .mkRegular {
  form := "wrench"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .pushPull }

/-- "fling" — verb of exerting force / throwing (Levin 12/17,
    @cite{levin-2026} (31)). Irregular past. -/
def fling : VerbEntry where
  form := "fling"
  form3sg := "flings"
  formPast := "flung"
  formPastPart := "flung"
  formPresPart := "flinging"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .pushPull

/-- "slam" — verb of surface contact, hitting (Levin 18.1,
    @cite{levin-2026} (32a)). Irregular doubling. -/
def slam : VerbEntry where
  form := "slam"
  form3sg := "slams"
  formPast := "slammed"
  formPastPart := "slammed"
  formPresPart := "slamming"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit

/-- "punch" — verb of surface contact, hitting (Levin 18.1,
    @cite{levin-2026} (32a)) -/
def punch : VerbEntry := .mkRegular {
  form := "punch"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "smack" — verb of surface contact, hitting (Levin 18.1,
    @cite{levin-2026} (32a)) -/
def smack : VerbEntry := .mkRegular {
  form := "smack"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "thump" — verb of surface contact, hitting (Levin 18.1,
    @cite{levin-2026} (32a)) -/
def thump : VerbEntry := .mkRegular {
  form := "thump"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "bang" — verb of surface contact, hitting (Levin 18.1,
    @cite{levin-2026} (32a)) -/
def bang : VerbEntry := .mkRegular {
  form := "bang"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "thrash" — verb of surface contact, hitting (Levin 18.1,
    @cite{levin-2026} (32a)) -/
def thrash : VerbEntry := .mkRegular {
  form := "thrash"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .hit }

/-- "scrape" — verb of surface contact, wiping (Levin 10.4,
    @cite{levin-2026} (32b)). In intr-push-open, enters through
    surface-contact sense, not removing sense. -/
def scrape : VerbEntry := .mkRegular {
  form := "scrape"
  complementType := .np
  vendlerClass := some .activity
  levinClass := some .wipe }

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : VerbEntry where
  form := "carry"
  form3sg := "carries"
  formPast := "carried"
  formPastPart := "carried"
  formPresPart := "carrying"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .carry

/-- "drag" — AgPat verb (Levin 11.4/12) -/
def drag : VerbEntry where
  form := "drag"
  form3sg := "drags"
  formPast := "dragged"
  formPastPart := "dragged"
  formPresPart := "dragging"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .carry

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : VerbEntry := .mkRegular {
  form := "call"
  complementType := .np
  vendlerClass := some .activity }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Putting (§ 9)
-- ════════════════════════════════════════════════════

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : VerbEntry := .mkRegular {
  form := "place"
  complementType := .np_pp
  vendlerClass := some .achievement
  levinClass := some .put }

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : VerbEntry := .mkRegular {
  form := "pour"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pour }

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : VerbEntry := .mkRegular {
  form := "spray"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .sprayLoad }

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : VerbEntry := .mkRegular {
  form := "load"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .sprayLoad }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Removing (§ 10)
-- ════════════════════════════════════════════════════

/-- "remove" — Levin 10.1 Remove verbs. -/
def remove : VerbEntry := .mkRegular {
  form := "remove"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .remove }

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : VerbEntry := .mkRegular {
  form := "clean"
  complementType := .np
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "cleanliness",
    baseAdjective := some "clean" }
  verbIncClass := some .sinc
  levinClass := some .clear }

/-- "steal" — Levin 10.5 Steal verbs. -/
def steal : VerbEntry where
  form := "steal"
  form3sg := "steals"
  formPast := "stole"
  formPastPart := "stolen"
  formPresPart := "stealing"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .steal

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Sending and Carrying (§ 11)
-- ════════════════════════════════════════════════════

/-- "send" — Levin 11.1 Send verbs. Alternates DOC/PP.
    Goal does not entail possession (prospective). Neither object implicit alone. -/
def send : VerbEntry where
  form := "send"
  form3sg := "sends"
  formPast := "sent"
  formPastPart := "sent"
  formPresPart := "sending"
  complementType := .np
  altComplementType := some .np_np
  implicitGoal := some .def
  vendlerClass := some .accomplishment
  levinClass := some .send

/-- "drive" — Levin 11.5 Drive verbs (vehicle-mediated motion). -/
def drive : VerbEntry where
  form := "drive"
  form3sg := "drives"
  formPast := "drove"
  formPastPart := "driven"
  formPresPart := "driving"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .drive

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Change of Possession (§ 13)
-- ════════════════════════════════════════════════════

/-- "donate" — Levin 13.2 Contribute verbs. -/
def donate : VerbEntry := .mkRegular {
  form := "donate"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .contribute }

/-- "obtain" — Levin 13.5 Get verbs. -/
def obtain : VerbEntry := .mkRegular {
  form := "obtain"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .getObtain }

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : VerbEntry := .mkRegular {
  form := "trade"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .exchange }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Learn, Hold, Conceal (§ 14–16)
-- ════════════════════════════════════════════════════

/-- "learn" — Levin 14 Learn verbs. -/
def learn : VerbEntry := .mkRegular {
  form := "learn"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .learn }

/-- "hold" — Levin 15.1 Hold verbs. Stative. -/
def hold : VerbEntry where
  form := "hold"
  form3sg := "holds"
  formPast := "held"
  formPastPart := "held"
  formPresPart := "holding"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .hold

/-- "hide" — Levin 16 Conceal verbs. -/
def hide : VerbEntry where
  form := "hide"
  form3sg := "hides"
  formPast := "hid"
  formPastPart := "hidden"
  formPresPart := "hiding"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .conceal

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Throwing (§ 17)
-- ════════════════════════════════════════════════════

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. Alternates DOC/PP.
    Implicit DO in PP frame only (definite). -/
def throw : VerbEntry where
  form := "throw"
  form3sg := "throws"
  formPast := "threw"
  formPastPart := "thrown"
  formPresPart := "throwing"
  complementType := .np
  altComplementType := some .np_np
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .achievement
  levinClass := some .throw

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Contact (§ 19–20)
-- ════════════════════════════════════════════════════

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : VerbEntry := .mkRegular {
  form := "poke"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .poke }

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : VerbEntry := .mkRegular {
  form := "touch"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .touch }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Cutting (§ 21)
-- ════════════════════════════════════════════════════

/-- "cut" — Levin 21.1 Cut verbs. Incremental by length of cut.
    @cite{majid-boster-bowerman-2008}: Dimension 1 high predictability —
    sharp instrument on yielding object → predictable locus of separation. -/
def cut : VerbEntry where
  form := "cut"
  form3sg := "cuts"
  formPast := "cut"
  formPastPart := "cut"
  formPresPart := "cutting"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .cut
  rootProfile := some {
    resultType := some [.surfaceBreach]
    instrumentType := some [.sharpBlade]
  }

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : VerbEntry where
  form := "chop"
  form3sg := "chops"
  formPast := "chopped"
  formPastPart := "chopped"
  formPresPart := "chopping"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .carve

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Combining and Separating (§ 22–23)
-- ════════════════════════════════════════════════════

/-- "mix" — Levin 22.1 Mix verbs. Incremental by proportion combined. -/
def mix : VerbEntry := .mkRegular {
  form := "mix"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .mix }

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : VerbEntry := .mkRegular {
  form := "separate"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .separate }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Coloring and Image Creation (§ 24–25)
-- ════════════════════════════════════════════════════

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : VerbEntry := .mkRegular {
  form := "paint"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .color }

/-- "draw" — Levin 25 Image Creation verbs. Incremental by extent. -/
def draw : VerbEntry where
  form := "draw"
  form3sg := "draws"
  formPast := "drew"
  formPastPart := "drawn"
  formPresPart := "drawing"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .imageCreation

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Creation and Transformation (§ 26)
-- ════════════════════════════════════════════════════

/-- "create" — Levin 26.4 Create verbs. -/
def create : VerbEntry := .mkRegular {
  form := "create"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .create }

/-- "grow" — Levin 26.2 Grow verbs. Incremental by size. -/
def grow : VerbEntry where
  form := "grow"
  form3sg := "grows"
  formPast := "grew"
  formPastPart := "grown"
  formPresPart := "growing"
  complementType := .np
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .grow

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : VerbEntry := .mkRegular {
  form := "perform"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .performance }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Predicative Complements (§ 29)
-- ════════════════════════════════════════════════════

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : VerbEntry := .mkRegular {
  form := "appoint"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .appoint }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Perception (§ 30)
-- ════════════════════════════════════════════════════

/-- "hear" — Levin 30.1 See verbs. Stative perception. Also embeds
    finite clauses (optionally factive per @cite{degen-tonhauser-2022}). -/
def hear : VerbEntry where
  form := "hear"
  form3sg := "hears"
  formPast := "heard"
  formPastPart := "heard"
  formPresPart := "hearing"
  complementType := .np
  altComplementType := some .finiteClause
  vendlerClass := some .state
  levinClass := some .see

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Judgment and Assessment (§ 33–34)
-- ════════════════════════════════════════════════════

/-- "blame" — Levin 33 Judgment verbs. -/
def blame : VerbEntry := .mkRegular {
  form := "blame"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .judgment }

/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : VerbEntry := .mkRegular {
  form := "evaluate"
  complementType := .np
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .assessment }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Social Interaction (§ 36)
-- ════════════════════════════════════════════════════

/-- "marry" — Levin 36 Social Interaction verbs. -/
def marry : VerbEntry where
  form := "marry"
  form3sg := "marries"
  formPast := "married"
  formPastPart := "married"
  formPresPart := "marrying"
  complementType := .np
  vendlerClass := some .achievement
  levinClass := some .socialInteraction

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Animal Sounds (§ 38)
-- ════════════════════════════════════════════════════

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : VerbEntry := .mkRegular {
  form := "bark"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .animalSound }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Body (§ 40–41)
-- ════════════════════════════════════════════════════

/-- "breathe" — Levin 40.1 Body Process verbs. -/
def breathe : VerbEntry := .mkRegular {
  form := "breathe"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .bodyProcess }

/-- "cough" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary event, no result state (@cite{smith-1997} §2.4.3). -/
def cough : VerbEntry := .mkRegular {
  form := "cough"
  complementType := .none
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .bodyProcess }

/-- "hiccup" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary body event (@cite{smith-1997} §2.4.3). -/
def hiccup : VerbEntry := .mkRegular {
  form := "hiccup"
  complementType := .none
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .bodyProcess }

/-- "blink" — Levin 40.3 Body-Internal Motion.
    Semelfactive: single instantaneous eye movement (@cite{smith-1997} §2.4.3). -/
def blink : VerbEntry := .mkRegular {
  form := "blink"
  complementType := .none
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .bodyProcess }

/-- "knock" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single percussive contact event
    (@cite{smith-1997} §2.4.3: "Guy knocked at the door"). -/
def knock : VerbEntry := .mkRegular {
  form := "knock"
  complementType := .none
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .hit }

/-- "tap" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single light percussive contact event (@cite{smith-1997} §2.4.3). -/
def tap : VerbEntry := .mkRegular {
  form := "tap"
  complementType := .none
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .hit }

/-- "flash" — Levin 43.1 Light Emission verbs.
    Semelfactive: single instantaneous light event (@cite{smith-1997} §2.4.3). -/
def flash : VerbEntry := .mkRegular {
  form := "flash"
  complementType := .none
  passivizable := false
  vendlerClass := some .semelfactive
  levinClass := some .lightEmission }

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : VerbEntry := .mkRegular {
  form := "flinch"
  complementType := .none
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .flinch }

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : VerbEntry := .mkRegular {
  form := "dress"
  complementType := .np
  vendlerClass := some .accomplishment
  levinClass := some .dress }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Killing (§ 42)
-- ════════════════════════════════════════════════════

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : VerbEntry := .mkRegular {
  form := "drown"
  complementType := .np
  vendlerClass := some .accomplishment
  causative := some .make
  levinClass := some .poison }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Emission (§ 43)
-- ════════════════════════════════════════════════════

/-- "glow" — Levin 43.1 Light Emission verbs. -/
def glow : VerbEntry := .mkRegular {
  form := "glow"
  complementType := .none
  passivizable := false
  vendlerClass := some .state
  unaccusative := true
  levinClass := some .lightEmission }

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : VerbEntry := .mkRegular {
  form := "buzz"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .soundEmission }

/-- "bleed" — Levin 43.4 Substance Emission verbs. -/
def bleed : VerbEntry where
  form := "bleed"
  form3sg := "bleeds"
  formPast := "bled"
  formPastPart := "bled"
  formPresPart := "bleeding"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  unaccusative := true
  levinClass := some .substanceEmission

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Change of State (§ 45)
-- ════════════════════════════════════════════════════

/-- "bend" — Levin 45.2 Bend verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (straight → bent, has maximal endpoint). -/
def bend : VerbEntry where
  form := "bend"
  form3sg := "bends"
  formPast := "bent"
  formPastPart := "bent"
  formPresPart := "bending"
  complementType := .np
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "curvature" }
  causative := some .make
  levinClass := some .bend

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : VerbEntry := .mkRegular {
  form := "boil"
  complementType := .np
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "temperature",
    baseAdjective := some "hot" }
  causative := some .make
  levinClass := some .cooking }

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : VerbEntry := .mkRegular {
  form := "rust"
  complementType := .none
  passivizable := false
  unaccusative := true
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "corrosion" }
  levinClass := some .entitySpecificCoS }

/-- "increase" — Levin 45.6 Calibratable CoS verbs (degree achievements).
    Degree achievement: open scale (no maximum quantity). -/
def increase : VerbEntry := .mkRegular {
  form := "increase"
  complementType := .np
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "quantity" }
  levinClass := some .calibratableCoS }

-- ════════════════════════════════════════════════════
-- § Degree Achievement Verb Pairs (@cite{kennedy-2007})
-- ════════════════════════════════════════════════════

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : VerbEntry := .mkRegular {
  form := "straighten"
  complementType := .np
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "straightness",
    baseAdjective := some "straight" }
  levinClass := some .otherCoS }

/-- "flatten" — Closed-scale degree achievement (base adj: flat).
    Accomplishment: "flattened the dough in 2 minutes." -/
def flatten : VerbEntry := .mkRegular {
  form := "flatten"
  complementType := .np
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "flatness",
    baseAdjective := some "flat" }
  levinClass := some .otherCoS }

/-- "open" — Closed-scale degree achievement (base adj: open, closed scale).
    Accomplishment: "opened the door in 3 seconds." -/
def open_ : VerbEntry := .mkRegular {
  form := "open"
  complementType := .np
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "openness",
    baseAdjective := some "open" }
  levinClass := some .otherCoS }

/-- "lengthen" — Open-scale degree achievement (base adj: long, open scale).
    Activity: "lengthened the rope for hours." -/
def lengthen : VerbEntry := .mkRegular {
  form := "lengthen"
  complementType := .np
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "length",
    baseAdjective := some "long" }
  levinClass := some .calibratableCoS }

/-- "widen" — Open-scale degree achievement (base adj: wide, open scale).
    Activity: "widened the road for months." -/
def widen : VerbEntry := .mkRegular {
  form := "widen"
  complementType := .np
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "width",
    baseAdjective := some "wide" }
  levinClass := some .calibratableCoS }

/-- "cool" — Open-scale degree achievement (base adj: cool, open scale).
    Activity: "cooled for an hour." -/
def cool : VerbEntry := .mkRegular {
  form := "cool"
  complementType := .np
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "temperature",
    baseAdjective := some "cool" }
  levinClass := some .otherCoS }

/-- "warm" — Open-scale degree achievement (base adj: warm, open scale).
    Activity: "warmed for an hour." -/
def warm : VerbEntry := .mkRegular {
  form := "warm"
  complementType := .np
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "temperature",
    baseAdjective := some "warm" }
  levinClass := some .otherCoS }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Existence, Appearance, Position (§ 47–50)
-- ════════════════════════════════════════════════════

/-- "exist" — Levin 47.1 Exist verbs. Pure state. -/
def exist : VerbEntry := .mkRegular {
  form := "exist"
  complementType := .none
  passivizable := false
  vendlerClass := some .state
  unaccusative := true
  levinClass := some .exist }

/-- "appear" — Levin 48.1 Appear verbs. Punctual emergence. -/
def appear : VerbEntry := .mkRegular {
  form := "appear"
  complementType := .none
  passivizable := false
  vendlerClass := some .achievement
  unaccusative := true
  levinClass := some .appear }

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : VerbEntry := .mkRegular {
  form := "fidget"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .bodyInternalMotion }

/-- "sit" — Levin 50 Assume Position verbs. Stative. -/
def sit : VerbEntry where
  form := "sit"
  form3sg := "sits"
  formPast := "sat"
  formPastPart := "sat"
  formPresPart := "sitting"
  complementType := .none
  passivizable := false
  vendlerClass := some .state
  levinClass := some .assumePosition

/-- "stand" — Levin 50 Assume Position verbs. Stative. -/
def stand : VerbEntry where
  form := "stand"
  form3sg := "stands"
  formPast := "stood"
  formPastPart := "stood"
  formPresPart := "standing"
  complementType := .none
  passivizable := false
  vendlerClass := some .state
  levinClass := some .assumePosition

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Motion (§ 51)
-- ════════════════════════════════════════════════════

/-- "walk" — Levin 51.3 Manner of Motion verbs. -/
def walk : VerbEntry := .mkRegular {
  form := "walk"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion }

/-- "swim" — Levin 51.3 Manner of Motion verbs. -/
def swim : VerbEntry where
  form := "swim"
  form3sg := "swims"
  formPast := "swam"
  formPastPart := "swum"
  formPresPart := "swimming"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .mannerOfMotion

/-- "fly" — Levin 51.4 Vehicle Motion verbs. -/
def fly : VerbEntry where
  form := "fly"
  form3sg := "flies"
  formPast := "flew"
  formPastPart := "flown"
  formPresPart := "flying"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .vehicleMotion

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Avoid, Linger, Rush (§ 52–53)
-- ════════════════════════════════════════════════════

/-- "avoid" — Levin 52 Avoid verbs. Stative. -/
def avoid : VerbEntry := .mkRegular {
  form := "avoid"
  complementType := .np
  vendlerClass := some .state
  levinClass := some .avoid }

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : VerbEntry := .mkRegular {
  form := "linger"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .linger }

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : VerbEntry := .mkRegular {
  form := "rush"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .rush }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Weather (§ 57)
-- ════════════════════════════════════════════════════

/-- "rain" — Levin 57 Weather verbs. Expletive subject. -/
def rain : VerbEntry := .mkRegular {
  form := "rain"
  complementType := .none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .weather }

-- ════════════════════════════════════════════════════
-- § Ditransitive Verbs — Implicit Arguments (@cite{bruening-2021})
-- ════════════════════════════════════════════════════

/-! Ditransitive verbs classified by their implicit argument behavior,
    following @cite{bruening-2021} Table (56). The classification is
    theory-neutral: it records surface optionality and interpretation
    without committing to a specific structural analysis. -/

-- DOC-only verbs (no PP frame alternant)

/-- "charge" — DOC-only. Implicit second obj indef, implicit goal def (addressee). -/
def charge : VerbEntry := .mkRegular {
  form := "charge"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "cost" — DOC-only. Implicit second obj indef, implicit goal def. -/
def cost : VerbEntry := .mkRegular {
  form := "cost"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .state }

/-- "fine" — DOC-only. Implicit second obj indef, implicit goal def. -/
def fine : VerbEntry := .mkRegular {
  form := "fine"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "tip" — DOC-only. Implicit second obj indef, implicit goal def (unique). -/
def tip : VerbEntry where
  form := "tip"
  form3sg := "tips"
  formPast := "tipped"
  formPastPart := "tipped"
  formPresPart := "tipping"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "pay" — DOC-only. Implicit second obj indef, implicit goal def. -/
def pay : VerbEntry where
  form := "pay"
  form3sg := "pays"
  formPast := "paid"
  formPastPart := "paid"
  formPresPart := "paying"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "strike" — DOC-only. Implicit second obj indef, implicit goal def (familiar). -/
def strike_ : VerbEntry where
  form := "strike"
  form3sg := "strikes"
  formPast := "struck"
  formPastPart := "struck"
  formPresPart := "striking"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .achievement
  senseTag := .default

/-- "forgive" — DOC-only. Implicit second obj def, implicit goal def (addressee). -/
def forgive : VerbEntry where
  form := "forgive"
  form3sg := "forgives"
  formPast := "forgave"
  formPastPart := "forgiven"
  formPresPart := "forgiving"
  complementType := .np_np
  implicitObj := some .def
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "spare" — DOC-only. Implicit second obj def, no implicit goal. -/
def spare : VerbEntry := .mkRegular {
  form := "spare"
  complementType := .np_np
  implicitObj := some .def
  vendlerClass := some .accomplishment }

/-- "deny" — DOC-only. Implicit second obj indef, implicit goal def. -/
def deny : VerbEntry where
  form := "deny"
  form3sg := "denies"
  formPast := "denied"
  formPastPart := "denied"
  formPresPart := "denying"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "permit" — DOC-only. Implicit second obj indef, implicit goal def (addressee). -/
def permit : VerbEntry where
  form := "permit"
  form3sg := "permits"
  formPast := "permitted"
  formPastPart := "permitted"
  formPresPart := "permitting"
  complementType := .np_np
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment

/-- "assign" — DOC-only. Implicit second obj indef, implicit goal def. -/
def assign : VerbEntry := .mkRegular {
  form := "assign"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

-- DOC-only verbs with no implicit arguments

/-- "begrudge" — DOC-only. Neither object implicit. -/
def begrudge : VerbEntry := .mkRegular {
  form := "begrudge"
  complementType := .np_np
  vendlerClass := some .state }

/-- "bet" — DOC-only. Neither object implicit. -/
def bet : VerbEntry where
  form := "bet"
  form3sg := "bets"
  formPast := "bet"
  formPastPart := "bet"
  formPresPart := "betting"
  complementType := .np_np
  vendlerClass := some .accomplishment

-- Alternating verbs (both DOC and PP frame)

/-- "serve" — alternates DOC/PP. Implicit second obj indef (DOC).
    Implicit goal def (PP). -/
def serve : VerbEntry := .mkRegular {
  form := "serve"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitObj := some .indef
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "teach" — alternates DOC/PP. Implicit goal indef (PP).
    When both implicit, both are indefinite. -/
def teach : VerbEntry where
  form := "teach"
  form3sg := "teaches"
  formPast := "taught"
  formPastPart := "taught"
  formPresPart := "teaching"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitObj := some .indef
  implicitGoal := some .indef
  vendlerClass := some .activity

/-- "feed" — alternates DOC/PP. Implicit second obj indef (DOC).
    No implicit goal. -/
def feed : VerbEntry where
  form := "feed"
  form3sg := "feeds"
  formPast := "fed"
  formPastPart := "fed"
  formPresPart := "feeding"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitObj := some .indef
  vendlerClass := some .activity

/-- "show" — alternates DOC/PP. Implicit second obj def. No implicit goal. -/
def show_ : VerbEntry where
  form := "show"
  form3sg := "shows"
  formPast := "showed"
  formPastPart := "shown"
  formPresPart := "showing"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitObj := some .def
  vendlerClass := some .accomplishment

/-- "award" — alternates DOC/PP. Implicit goal def (PP). -/
def award : VerbEntry := .mkRegular {
  form := "award"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "forward" — alternates DOC/PP. Implicit goal def (PP). -/
def forward_ : VerbEntry := .mkRegular {
  form := "forward"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "grant" — alternates DOC/PP. Implicit goal def (PP). -/
def grant : VerbEntry := .mkRegular {
  form := "grant"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "offer" — alternates DOC/PP. Implicit goal def (PP). -/
def offer : VerbEntry := .mkRegular {
  form := "offer"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "reserve" — alternates DOC/PP. Implicit goal def (PP). -/
def reserve : VerbEntry := .mkRegular {
  form := "reserve"
  complementType := .np_np
  altComplementType := some .np_pp
  implicitGoal := some .def
  vendlerClass := some .accomplishment }

/-- "pass" — alternates DOC/PP. Implicit DO def in PP frame only. -/
def pass : VerbEntry := .mkRegular {
  form := "pass"
  complementType := .np
  altComplementType := some .np_pp
  implicitObj := some .def
  implicitGoal := some .indef
  vendlerClass := some .accomplishment
  levinClass := some .give }

-- Alternating verbs with no implicit arguments

/-- "hand" — alternates DOC/PP. Neither argument implicit. -/
def hand : VerbEntry := .mkRegular {
  form := "hand"
  complementType := .np_np
  altComplementType := some .np_pp
  vendlerClass := some .accomplishment
  levinClass := some .give }

/-- "lend" — alternates DOC/PP. Neither argument implicit. -/
def lend : VerbEntry where
  form := "lend"
  form3sg := "lends"
  formPast := "lent"
  formPastPart := "lent"
  formPresPart := "lending"
  complementType := .np_np
  altComplementType := some .np_pp
  vendlerClass := some .accomplishment
  levinClass := some .give

-- ════════════════════════════════════════════════════
-- § Verb List and Lookup
-- ════════════════════════════════════════════════════

/-- Get all verb entries as a list (for enumeration). -/
def allVerbs : List VerbEntry := [
  -- Simple
  sleep, run, arrive, eat, kick, give, put, buy, meet, sell, leave, see, devour, read,
  build, write, sweep, sweep_instr,
  -- Factive
  know, regret, realize, discover, notice,
  -- Change of State
  stop, quit, start, begin_, continue_, keep,
  -- Implicative / Control
  manage, fail, try_, persuade, promise, remember, forget, neglect,
  -- Doxastic Attitude
  believe, think,
  -- Preferential Attitude (@cite{qing-uegaki-2025})
  want, hope, expect, wish,
  fear, dread,
  worry,
  -- Raising
  seem,
  -- Causative (@cite{nadathur-lauer-2020} + @cite{wolff-2003})
  cause,
  make,
  let_, have_caus, get_caus, force, prevent,
  -- Lexical causatives (Martin, @cite{martin-rose-nichols-2025})
  kill, break_, tear_, burn, destroy, melt,
  activate, affect, change, damage, eliminate, hurt, restore, trigger,
  bury, drop, lift, lock, shut, spread, stretch, switch,
  -- Communication
  say, tell, claim,
  -- Clause-Embedding (@cite{degen-tonhauser-2021})
  reveal, acknowledge, admit, announce, confess, inform, suggest,
  pretend, confirm, demonstrate, establish, prove,
  -- Manner of Speaking (@cite{storment-2026})
  whisper, murmur, shout, cry, scream, speak, talk,
  -- Question-embedding (@cite{dayal-2025})
  wonder, ask, investigate, depend_on,
  -- Factive question-embedding senses
  remember_rog, forget_rog,
  -- Occasion Verbs (@cite{solstad-bott-2024})
  manage_occasion, dare, bother, hesitate, venture, condescend, happen,
  -- Agent-Experiencer (@cite{solstad-bott-2024})
  enjoy, like, love, hate, admire, envy, respect, value,
  -- Stimulus-Experiencer (@cite{solstad-bott-2024})
  frighten, amuse, fascinate, irritate, annoy, bore, charm, impress,
  -- Stative Class II (@cite{kim-2024} UPH)
  concern, interest,
  -- Agent-Patient (@cite{solstad-bott-2024})
  chase, hit, push, pull, carry, drag, call,
  -- Levin § 12 Push/Pull (exerting force, @cite{levin-2026})
  shove, tug, yank, jerk, wrench, fling,
  -- Levin § 18.1 Hit (surface contact, @cite{levin-2026})
  slam, punch, smack, thump, bang, thrash,
  -- Levin § 10.4 Wipe (surface contact, @cite{levin-2026})
  scrape,
  -- Levin § 9 Putting
  place, pour, spray, load,
  -- Levin § 10 Removing
  remove, clean, steal,
  -- Levin § 11 Sending and Carrying
  send, drive,
  -- Levin § 13 Change of Possession
  donate, obtain, trade,
  -- Levin § 14–16 Learn, Hold, Conceal
  learn, hold, hide,
  -- Levin § 17 Throwing
  throw,
  -- Ditransitive — implicit arguments (@cite{bruening-2021})
  charge, cost, fine, tip, pay, strike_, forgive, spare, deny, permit, assign,
  begrudge, bet, serve, teach, feed, show_, award, forward_, grant, offer,
  reserve, pass, hand, lend,
  -- Levin § 19–20 Contact
  poke, touch,
  -- Levin § 21 Cutting
  cut, chop,
  -- Levin § 22–23 Combining, Separating
  mix, separate,
  -- Levin § 24–25 Coloring, Image Creation
  paint, draw,
  -- Levin § 26 Creation and Transformation
  create, grow, perform,
  -- Levin § 29 Predicative Complements
  appoint,
  -- Levin § 30 Perception
  hear,
  -- Levin § 33–34 Judgment, Assessment
  blame, evaluate,
  -- Levin § 36 Social Interaction
  marry,
  -- Levin § 38 Animal Sounds
  bark,
  -- Levin § 40–41 Body, Grooming
  breathe, cough, flinch, dress,
  -- Levin § 42 Killing
  drown,
  -- Levin § 43 Emission
  glow, buzz, bleed,
  -- Levin § 45 Change of State
  bend, boil, rust, increase,
  -- Degree Achievement Pairs (@cite{kennedy-2007})
  straighten, flatten, open_, lengthen, widen, cool, warm,
  -- Levin § 47–50 Existence, Appearance, Position
  exist, appear, fidget, sit, stand,
  -- Levin § 51 Motion
  walk, swim, fly,
  -- Levin § 52–53 Avoid, Linger, Rush
  avoid, linger, rush,
  -- Levin § 57 Weather
  rain
]

/-- Look up a verb entry by citation form. -/
def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (λ v => v.form == form)

-- ════════════════════════════════════════════════════
-- § Word Conversion
-- ════════════════════════════════════════════════════

/-- Convert a verb entry to a `Word` (from Core.Basic) in 3sg present form. -/
def VerbEntry.toWord3sg (v : VerbEntry) : Word :=
  { form := v.form3sg
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , number := some .sg
      , person := some .third
      , voice := some .active
      , vform := some .finite
      , tense := some .present
    }
  }

/-- Convert a verb entry to a `Word` in base/plural present form. -/
def VerbEntry.toWordPl (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , number := some .pl
      , tense := some .present
    }
  }

/-- Convert a verb entry to a `Word` in base/infinitive form. -/
def VerbEntry.toWordBase (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , vform := some .infinitive
    }
  }

/-- Convert a verb entry to a `Word` in past tense (active finite) form. -/
def VerbEntry.toWordPast (v : VerbEntry) : Word :=
  { form := v.formPast
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , vform := some .finite
      , voice := some .active
      , tense := some .past
    }
  }

/-- Convert a verb entry to a `Word` in past participle form.
    Retains original valence (for perfects: "has kicked the ball").
    For passive constructions, compose with `Word.asPassive`:
    `v.toWordPastPart.asPassive`. -/
def VerbEntry.toWordPastPart (v : VerbEntry) : Word :=
  { form := v.formPastPart
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , vform := some .pastParticiple
    }
  }

/-- Convert a verb entry to a `Word` in present participle form. -/
def VerbEntry.toWordPresPart (v : VerbEntry) : Word :=
  { form := v.formPresPart
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , vform := some .presParticiple
    }
  }

-- ════════════════════════════════════════════════════
-- § Causative Grounding Theorems
-- ════════════════════════════════════════════════════

/-! These verify that the Fragment's causative annotations are consistent
with the formal semantics in `Semantics.Causation`.

The semantic-dispatch grounding theorems (e.g., `make_semantics`,
`cause_semantics`, `prevent_semantics`, `sufficiency_verbs_share_truth_conditions`,
`lexical_causatives_match_make`) are in the `V2` sub-namespace below,
parameterized by an arbitrary `SEM V α`. The legacy versions (which
referenced `Causative.toSemantics` over `CausalDynamics`) were removed
in Phase D-G in favor of the polymorphic V2 versions. -/

/-- "make" asserts sufficiency — derived from its builder. -/
theorem make_asserts_sufficiency : make.toVerbCore.assertsSufficiency = true := by native_decide

/-- "cause" asserts necessity — derived from its builder. -/
theorem cause_asserts_necessity : cause.toVerbCore.assertsNecessity = true := by native_decide

/-- "make" does NOT assert necessity. -/
theorem make_not_necessity : make.toVerbCore.assertsNecessity = false := by native_decide

/-- "cause" does NOT assert sufficiency. -/
theorem cause_not_sufficiency : cause.toVerbCore.assertsSufficiency = false := by native_decide

/-- make-type verbs (make, have, get) share the `.make` builder. -/
theorem make_type_verbs_share_semantics :
    make.causative = have_caus.causative ∧
    make.causative = get_caus.causative := ⟨rfl, rfl⟩

/-- "force" is coercive — derived from its builder. -/
theorem force_is_coercive :
    force.causative.map (·.isCoercive) = some true := rfl

/-- "let" is permissive — derived from its builder. -/
theorem let_is_permissive :
    let_.causative.map (·.isPermissive) = some true := rfl

/-- "prevent" asserts neither sufficiency nor necessity —
    it uses the dual `preventSem` (blocking). -/
theorem prevent_not_sufficiency :
    prevent.toVerbCore.assertsSufficiency = false := by native_decide

/-- "prevent" is an EN trigger — it entails ¬p in w₀ (complement
    falsity), satisfying the FORGET class licensing condition
    (@cite{jin-koenig-2021}, §6.1.4). -/
theorem prevent_is_en_trigger :
    prevent.toVerbCore.isENTrigger = true := rfl

/-- make, force, and let have different builders despite shared truth conditions. -/
theorem causative_builders_distinguished :
    make.causative ≠ force.causative ∧
    make.causative ≠ let_.causative ∧
    force.causative ≠ let_.causative := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Lexical causative theorems -/

/-- All lexical causatives use the `.make` builder. -/
theorem lexical_causatives_use_make :
    kill.causative = some .make ∧
    break_.causative = some .make ∧
    burn.causative = some .make ∧
    destroy.causative = some .make ∧
    melt.causative = some .make := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Lexical causatives all assert sufficiency — like periphrastic "make". -/
theorem lexical_causatives_assert_sufficiency :
    kill.toVerbCore.assertsSufficiency = true ∧
    break_.toVerbCore.assertsSufficiency = true ∧
    burn.toVerbCore.assertsSufficiency = true ∧
    destroy.toVerbCore.assertsSufficiency = true ∧
    melt.toVerbCore.assertsSufficiency = true := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

/-- Lexical causatives differ from periphrastic "cause" in truth conditions. -/
theorem lexical_causatives_differ_from_cause :
    kill.causative ≠ cause.causative ∧
    break_.causative ≠ cause.causative := by
  constructor <;> decide

-- ════════════════════════════════════════════════════
-- § Implicative Grounding Theorems
-- ════════════════════════════════════════════════════

/-! Semantic-dispatch grounding for implicatives is in the `V2`
sub-namespace (`manage_semantics_implicative`, `fail_semantics_implicative`)
parameterized by an arbitrary `SEM V α`. The legacy versions were
removed in Phase D-G. -/

/-- "manage" entails the complement — derived from its builder. -/
theorem manage_entails_complement_derived :
    manage.toVerbCore.entailsComplement = some true := by native_decide

/-- "fail" entails NOT the complement — derived from its builder. -/
theorem fail_entails_not_complement_derived :
    fail.toVerbCore.entailsComplement = some false := by native_decide

/-- "remember" entails the complement — derived from its builder. -/
theorem remember_entails_complement_derived :
    remember.toVerbCore.entailsComplement = some true := by native_decide

/-- "forget" entails NOT the complement — derived from its builder. -/
theorem forget_entails_not_complement_derived :
    forget.toVerbCore.entailsComplement = some false := by native_decide

-- ════════════════════════════════════════════════════
-- § Morphological Stem + Vacuity
-- ════════════════════════════════════════════════════

/-- Convert a `VerbEntry` to a morphological `Stem`.

    All verb inflection is semantically vacuous at the word level:
    tense/aspect semantics is compositional, handled by
    `Semantics.Intensional`. The `isVacuous := true` flags make
    this explicit. -/
def VerbEntry.toStem {σ : Type} (v : VerbEntry) : Core.Morphology.Stem σ :=
  { lemma_ := v.form
  , cat := .VERB
  , baseFeatures := { valence := some (complementToValence v.complementType)
                    , vform := some .infinitive }
  , paradigm :=
    [ { category := .agreement, value := "3sg"
      , formRule := λ _ => v.form3sg
      , featureRule := λ f => { f with number := some .Sing
                                     , person := some .third
                                     , vform := some .finite }
      , semEffect := id, isVacuous := true }
    , { category := .tense, value := "past"
      , formRule := λ _ => v.formPast
      , featureRule := λ f => { f with vform := some .finite }
      , semEffect := id, isVacuous := true }
    , { category := .tense, value := "pastpart"
      , formRule := λ _ => v.formPastPart
      , featureRule := λ f => { f with vform := some .pastParticiple }
      , semEffect := id, isVacuous := true }
    , { category := .aspect, value := "prespart"
      , formRule := λ _ => v.formPresPart
      , featureRule := λ f => { f with vform := some .presParticiple }
      , semEffect := id, isVacuous := true }
    ] }

/-- All verb inflectional rules are semantically vacuous. -/
theorem VerbEntry.toStem_allVacuous {σ : Type} (v : VerbEntry) :
    (v.toStem (σ := σ)).paradigm.all (·.isVacuous) = true := rfl

-- ════════════════════════════════════════════════════
-- § V2 Causative Grounding Theorems (Phase D-D)
-- ════════════════════════════════════════════════════

/-! V2 mirror of the rfl theorems above on the BoolSEM substrate.
Each statement is parameterized by an arbitrary deterministic acyclic
SEM `M`; `Causative.toSemantics M` dispatches to the V2 hub
predicates (`Sufficiency.makeSem`, `Necessity.causeSem`,
`Prevention.preventSem`). The legacy CausalDynamics-based
theorems above remain intact. -/

namespace V2

open Core.Causal (SEM CausalGraph Valuation DecidableValuation)
open Core.Verbs

variable {V : Type*} {α : V → Type*}
  [Fintype V] [DecidableEq V] [DecidableValuation α] [∀ v, Fintype (α v)]
  (M : SEM V α) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]

/-- V2 "make" → `Sufficiency.makeSem` (polymorphic). -/
theorem make_semantics :
    make.causative.map (Causative.toSemantics M) =
    some (Semantics.Causation.Sufficiency.makeSem M) := rfl

/-- V2 "cause" → `Necessity.causeSem` (polymorphic). -/
theorem cause_semantics :
    cause.causative.map (Causative.toSemantics M) =
    some (Semantics.Causation.Necessity.causeSem M) := rfl

/-- V2 "prevent" → `Prevention.preventSem` (polymorphic). -/
theorem prevent_semantics :
    prevent.causative.map (Causative.toSemantics M) =
    some (Semantics.Causation.Prevention.preventSem M) := rfl

/-- V2: make/force/let/have/get share `Sufficiency.makeSem` truth conditions. -/
theorem sufficiency_verbs_share_truth_conditions :
    make.causative.map (Causative.toSemantics M) =
      force.causative.map (Causative.toSemantics M) ∧
    make.causative.map (Causative.toSemantics M) =
      let_.causative.map (Causative.toSemantics M) ∧
    make.causative.map (Causative.toSemantics M) =
      have_caus.causative.map (Causative.toSemantics M) ∧
    make.causative.map (Causative.toSemantics M) =
      get_caus.causative.map (Causative.toSemantics M) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- V2: lexical causatives (kill, break) share truth conditions with periphrastic "make". -/
theorem lexical_causatives_match_make :
    kill.causative.map (Causative.toSemantics M) =
      make.causative.map (Causative.toSemantics M) ∧
    break_.causative.map (Causative.toSemantics M) =
      make.causative.map (Causative.toSemantics M) := ⟨rfl, rfl⟩

/-- "manage" → polymorphic `Implicative.manageSem`. -/
theorem manage_semantics_implicative :
    manage.implicative.map (Implicative.toSemantics M) =
    some (Semantics.Causation.Implicative.manageSem M) := rfl

/-- "fail" → polymorphic `Implicative.failSem`. -/
theorem fail_semantics_implicative :
    fail.implicative.map (Implicative.toSemantics M) =
    some (Semantics.Causation.Implicative.failSem M) := rfl

end V2

end Fragments.English.Predicates.Verbal
