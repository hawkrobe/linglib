import Linglib.Theories.Semantics.Lexical.Verb.VerbEntry
import Linglib.Core.Lexical.MorphRule

/-! # Verbal Predicate Lexicon Fragment

English verb lexical entries with morphology, argument structure, semantic class,
and links to compositional semantics (CoS, attitudes, causatives).

Semantic types (`ComplementType`, `AttitudeBuilder`, etc.) and the
cross-linguistic `VerbCore` structure live in `Core/Verbs.lean`. This file
defines `VerbEntry extends VerbCore` with English-specific inflectional fields
and provides smart constructors for regular verbs.
-/

namespace Fragments.English.Predicates.Verbal

-- Re-export Core.Verbs types so downstream files that open this namespace
-- (e.g., `open Fragments.English.Predicates.Verbal (ComplementType ...)`)
-- continue to find them.
export Core.Verbs (PreferentialBuilder AttitudeBuilder PresupTriggerType
  ComplementType ControlType VerbCore complementToValence)

open Core.Verbs
open NadathurLauer2020.Builder (CausativeBuilder)
open Nadathur2023.Implicative (ImplicativeBuilder)
open Semantics.Lexical.Verb.Aspect (VendlerClass)
open Semantics.Lexical.Verb.DegreeAchievement (DegreeAchievementScale)
open Core.Scale (Boundedness)
open Semantics.Events.Krifka1998 (VerbIncClass)

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
    def kick : VerbEntry := .mkRegular {
      form := "kick", complementType := .np,
      subjectTheta := some .agent, objectTheta := some .patient }
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .theme  -- Underlying object
  unaccusative := true
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .inherentlyDirectedMotion }

/-- "eat" — transitive, no presupposition -/
def eat : VerbEntry where
  form := "eat"
  form3sg := "eats"
  formPast := "ate"
  formPastPart := "eaten"
  formPresPart := "eating"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  levinClass := some .hit
  rootProfile := some {
    forceMag := some [.moderate, .high]
    forceDir := some [.unidirectional]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "give" — ditransitive -/
def give : VerbEntry where
  form := "give"
  form3sg := "gives"
  formPast := "gave"
  formPastPart := "given"
  formPresPart := "giving"
  complementType := .np_np
  subjectTheta := some .agent
  objectTheta := some .theme
  object2Theta := some .goal
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
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .achievement
  levinClass := some .put

/-- "weigh" — measure predicate selecting for mass/weight (Bale & Schwarz 2026). -/
def weigh : VerbEntry := .mkRegular {
  form := "weigh"
  complementType := .np
  subjectTheta := some .theme
  objectTheta := some .theme
  vendlerClass := some .state
  selectsDimension := some .mass
  levinClass := some .measure }

/-- "cover" — motion/extent predicate selecting for distance (Bale & Schwarz 2026). -/
def cover : VerbEntry := .mkRegular {
  form := "cover"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  selectsDimension := some .distance }

/-- "measure" — general measurement predicate. -/
def measure : VerbEntry := .mkRegular {
  form := "measure"
  complementType := .np
  subjectTheta := some .theme
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment

/-- "meet" — irregular transitive -/
def meet : VerbEntry where
  form := "meet"
  form3sg := "meets"
  formPast := "met"
  formPastPart := "met"
  formPresPart := "meeting"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .achievement

/-- "sell" — irregular transitive -/
def sell : VerbEntry where
  form := "sell"
  form3sg := "sells"
  formPast := "sold"
  formPastPart := "sold"
  formPresPart := "selling"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment

/-- "leave" — transitive (also used intransitively with argument drop) -/
def leave : VerbEntry where
  form := "leave"
  form3sg := "leaves"
  formPast := "left"
  formPastPart := "left"
  formPresPart := "leaving"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  factivePresup := true
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
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true
  complementSig := some .mono
  attitudeBuilder := some (.doxastic .veridical)

/-- "regret" — factive, presupposes complement is true -/
def regret : VerbEntry where
  form := "regret"
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  complementType := .finiteClause
  vendlerClass := some .state
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true

/-- "realize" — factive, presupposes complement is true -/
def realize : VerbEntry := .mkRegular {
  form := "realize"
  complementType := .finiteClause
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  attitudeBuilder := some (.doxastic .veridical) }

/-- "discover" — semifactive, weaker projection -/
def discover : VerbEntry := .mkRegular {
  form := "discover"
  complementType := .finiteClause
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true
  attitudeBuilder := some (.doxastic .veridical) }

/-- "notice" — semifactive -/
def notice : VerbEntry := .mkRegular {
  form := "notice"
  complementType := .finiteClause
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  attitudeBuilder := some (.doxastic .veridical) }

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
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
    See also `manage_occasion` for the Solstad & Bott (2024) analysis. -/
def manage : VerbEntry := .mkRegular {
  form := "manage"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  implicativeBuilder := some .positive }

/-- "fail" — negative implicative: "failed to VP" entails "not VP" -/
def fail : VerbEntry := .mkRegular {
  form := "fail"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  implicativeBuilder := some .negative }

/-- "try" — subject control, no entailment -/
def try_ : VerbEntry where
  form := "try"
  form3sg := "tries"
  formPast := "tried"
  formPastPart := "tried"
  formPresPart := "trying"
  complementType := .infinitival
  vendlerClass := some .activity
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false

/-- "persuade" — object control: "persuade X to VP" (X = agent of VP) -/
def persuade : VerbEntry := .mkRegular {
  form := "persuade"
  complementType := .infinitival
  vendlerClass := some .accomplishment
  subjectTheta := some .agent
  objectTheta := some .experiencer
  controlType := .objectControl }

/-- "promise" — subject control with object: "promise X to VP" -/
def promise : VerbEntry := .mkRegular {
  form := "promise"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .agent
  objectTheta := some .goal
  controlType := .subjectControl }

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : VerbEntry := .mkRegular {
  form := "remember"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  implicativeBuilder := some .positive }

/-- "forget" — negative implicative with infinitival -/
def forget : VerbEntry where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  implicativeBuilder := some .negative

-- ════════════════════════════════════════════════════
-- § Verb Entries — Doxastic Attitude
-- ════════════════════════════════════════════════════

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : VerbEntry := .mkRegular {
  form := "believe"
  complementType := .finiteClause
  vendlerClass := some .state
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.doxastic .nonVeridical)
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
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.doxastic .nonVeridical)
  complementSig := some .mono

-- ════════════════════════════════════════════════════
-- § Verb Entries — Preferential Attitude
-- ════════════════════════════════════════════════════

/-- "want" — preferential attitude verb with infinitival complement -/
def want : VerbEntry := .mkRegular {
  form := "want"
  complementType := .infinitival
  vendlerClass := some .state
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono
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
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono }

/-- "expect" — preferential attitude verb (Class 3: anti-rogative) -/
def expect : VerbEntry := .mkRegular {
  form := "expect"
  complementType := .finiteClause
  vendlerClass := some .state
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))
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
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))
  complementSig := some .mono
  levinClass := some .want

/-- "fear" — preferential attitude verb (Class 2: takes questions) -/
def fear : VerbEntry := .mkRegular {
  form := "fear"
  complementType := .finiteClause
  vendlerClass := some .state
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))
  complementSig := some .mono
  levinClass := some .admire }

/-- "dread" — preferential attitude verb (Class 2: takes questions) -/
def dread : VerbEntry := .mkRegular {
  form := "dread"
  complementType := .finiteClause
  vendlerClass := some .state
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative))
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
  subjectTheta := some .experiencer
  passivizable := false
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)
  complementSig := some .mono

-- ════════════════════════════════════════════════════
-- § Verb Entries — Raising
-- ════════════════════════════════════════════════════

/-- "seem" — raising verb (no theta role for subject, unaccusative) -/
def seem : VerbEntry := .mkRegular {
  form := "seem"
  complementType := .infinitival
  vendlerClass := some .state
  subjectTheta := none
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
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .cause
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
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make

/-- "let" — permissive causative (barrier removal) -/
def let_ : VerbEntry where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  complementType := .smallClause
  vendlerClass := some .achievement
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .enable

/-- "have" — causative use (directive causation) -/
def have_caus : VerbEntry where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  complementType := .smallClause
  vendlerClass := some .achievement
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make
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
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .make
  senseTag := .causative

/-- "force" — coercive causative (overcome resistance) -/
def force : VerbEntry := .mkRegular {
  form := "force"
  complementType := .infinitival
  vendlerClass := some .accomplishment
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  causativeBuilder := some .force }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Lexical Causatives
-- ════════════════════════════════════════════════════

/-- "kill" — thin lexical causative (kill = cause-to-die, COMPACT type). -/
def kill : VerbEntry := .mkRegular {
  form := "kill"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  causativeBuilder := some .make
  levinClass := some .murder
  rootProfile := some {
    resultType := some [.totalDestruction]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "break" — thick lexical causative (Levin 45.1 Break Verbs; Embick 2009 break-class).
    Pure change-of-state verb: change in "material integrity" (Hale & Keyser 1987)
    with no specification of how the change comes about (Levin 1993:242). -/
def break_ : VerbEntry where
  form := "break"
  form3sg := "breaks"
  formPast := "broke"
  formPastPart := "broken"
  formPresPart := "breaking"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  unaccusative := false
  vendlerClass := some .accomplishment
  causativeBuilder := some .make
  levinClass := some .break_
  rootProfile := some {
    forceMag := some [.moderate, .high]
    forceDir := some [.omnidirectional]
    patientRob := some [.moderate, .robust]
    resultType := some [.fracture]
    agentControl := some [.incompatible, .neutral]
  }

/-- "tear" — Levin 45.1 Break Verbs. Contrary-direction separation with force.
    Unlike *break*, *tear* implies a specific directionality (bidirectional /
    pulling apart) and is compatible with careful controlled action.
    Patient restriction: any solid capable of irregular separation.
    Spalek & McNally (forthcoming, §3.1–3.2). -/
def tear_ : VerbEntry where
  form := "tear"
  form3sg := "tears"
  formPast := "tore"
  formPastPart := "torn"
  formPresPart := "tearing"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  unaccusative := false
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causativeBuilder := some .make
  levinClass := some .break_
  rootProfile := some {
    forceMag := some [.moderate, .high]
    forceDir := some [.bidirectional, .unidirectional]
    patientRob := some [.flimsy, .moderate, .robust]
    resultType := some [.separation]
    agentControl := some [.neutral, .compatible]
  }

/-- "burn" — thick lexical causative (manner = by fire/heat). -/
def burn : VerbEntry := .mkRegular {
  form := "burn"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causativeBuilder := some .make
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  causativeBuilder := some .make
  levinClass := some .destroy
  rootProfile := some {
    resultType := some [.totalDestruction]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.neutral, .compatible]
  } }

/-- "melt" — thick lexical causative (manner = by heat). -/
def melt : VerbEntry := .mkRegular {
  form := "melt"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  causativeBuilder := some .make
  levinClass := some .otherCoS
  rootProfile := some {
    forceMag := some [.low, .moderate]
    patientRob := some [.moderate, .robust]
    resultType := some [.deformation]
    agentVolition := some [.neutral, .volitional]
    agentControl := some [.compatible]
  } }

-- ════════════════════════════════════════════════════
-- § Martin, Rose & Nichols (2025) — Thick/Thin Causatives
-- ════════════════════════════════════════════════════

-- Entries for causative verbs classified by Martin et al. (2025) that don't
-- already have Fragment entries elsewhere (break_, burn, destroy, melt, kill,
-- cut, mix, start, stop already defined above).

/-- "activate" — thin causative, CoS without manner. -/
def activate : VerbEntry := .mkRegular {
  form := "activate"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

/-- "affect" — thin causative, general effect. -/
def affect : VerbEntry := .mkRegular {
  form := "affect"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  levinClass := some .destroy }

/-- "change" — thin causative, transformation (§26.6). -/
def change : VerbEntry := .mkRegular {
  form := "change"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .turn }

/-- "damage" — thin causative, partial destruction. -/
def damage : VerbEntry := .mkRegular {
  form := "damage"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .destroy }

/-- "eliminate" — thin causative, removal/destruction. -/
def eliminate : VerbEntry := .mkRegular {
  form := "eliminate"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .destroy

/-- "restore" — thin causative, reverse transformation (§26.6). -/
def restore : VerbEntry := .mkRegular {
  form := "restore"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .turn }

/-- "trigger" — thin causative, engender class (§27). -/
def trigger : VerbEntry := .mkRegular {
  form := "trigger"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .achievement
  levinClass := some .engender }

/-- "bury" — thick causative (state), concealment (§16). -/
def bury : VerbEntry := .mkRegular {
  form := "bury"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .conceal }

/-- "drop" — thick causative, caused falling (§45.4). -/
def drop : VerbEntry := .mkRegular {
  form := "drop"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

/-- "lift" — thick causative, caused upward motion (§11.4 carry). -/
def lift : VerbEntry := .mkRegular {
  form := "lift"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .carry }

/-- "lock" — thick causative, caused secured state (§45.4). -/
def lock : VerbEntry := .mkRegular {
  form := "lock"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .sprayLoad

/-- "stretch" — thick causative, bend class (§45.2). -/
def stretch : VerbEntry := .mkRegular {
  form := "stretch"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .bend }

/-- "switch" — thick causative, CoS (§45.4). -/
def switch : VerbEntry := .mkRegular {
  form := "switch"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .otherCoS }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Other
-- ════════════════════════════════════════════════════

/-- "devour" — transitive, no presupposition -/
def devour : VerbEntry := .mkRegular {
  form := "devour"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .inc

/-- "build" — creation verb, strictly incremental theme -/
def build : VerbEntry where
  form := "build"
  form3sg := "builds"
  formPast := "built"
  formPastPart := "built"
  formPresPart := "building"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .build

/-- "write" — creation verb, strictly incremental theme -/
def write : VerbEntry where
  form := "write"
  form3sg := "writes"
  formPast := "wrote"
  formPastPart := "written"
  formPresPart := "writing"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc

/-- "sweep" — motion + sustained contact, variable agentivity (default sense). -/
def sweep : VerbEntry where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  complementType := .np
  vendlerClass := some .activity
  subjectTheta := none
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .theme
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
  levinClass := some .say

/-- "tell" — communication verb with recipient -/
def tell : VerbEntry where
  form := "tell"
  form3sg := "tells"
  formPast := "told"
  formPastPart := "told"
  formPresPart := "telling"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .achievement
  levinClass := some .tell

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : VerbEntry := .mkRegular {
  form := "claim"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .achievement
  levinClass := some .say }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Manner of Speaking (Levin 37.3)
-- ════════════════════════════════════════════════════

/-! Manner-of-speaking (MoS) verbs specify *how* something is said.
    Storment (2026, NLLT) shows these divide into two classes:
    - **QI-permitting** (unaccusative): whisper, murmur, mumble, mutter, shout,
      cry, scream, shriek, yell, groan, grumble, hiss, sigh, whimper, snap
    - **Non-QI** (unergative): speak, talk -/

/-- "whisper" — MoS verb, permits quotative inversion (unaccusative) -/
def whisper : VerbEntry := .mkRegular {
  form := "whisper"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "murmur" — MoS verb, permits quotative inversion (unaccusative) -/
def murmur : VerbEntry := .mkRegular {
  form := "murmur"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "shout" — MoS verb, permits quotative inversion (unaccusative) -/
def shout : VerbEntry := .mkRegular {
  form := "shout"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "cry" — MoS verb, permits quotative inversion (unaccusative) -/
def cry : VerbEntry := .mkRegular {
  form := "cry"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "scream" — MoS verb, permits quotative inversion (unaccusative) -/
def scream : VerbEntry := .mkRegular {
  form := "scream"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "mumble" — MoS verb, permits quotative inversion (unaccusative) -/
def mumble : VerbEntry := .mkRegular {
  form := "mumble"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "mutter" — MoS verb, permits quotative inversion (unaccusative) -/
def mutter : VerbEntry := .mkRegular {
  form := "mutter"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "shriek" — MoS verb, permits quotative inversion (unaccusative) -/
def shriek : VerbEntry := .mkRegular {
  form := "shriek"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "yell" — MoS verb, permits quotative inversion (unaccusative) -/
def yell : VerbEntry := .mkRegular {
  form := "yell"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "groan" — MoS verb, permits quotative inversion (unaccusative) -/
def groan : VerbEntry := .mkRegular {
  form := "groan"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "grumble" — MoS verb, permits quotative inversion (unaccusative) -/
def grumble : VerbEntry := .mkRegular {
  form := "grumble"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "hiss" — MoS verb, permits quotative inversion (unaccusative) -/
def hiss : VerbEntry := .mkRegular {
  form := "hiss"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "sigh" — MoS verb, permits quotative inversion (unaccusative) -/
def sigh : VerbEntry := .mkRegular {
  form := "sigh"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "whimper" — MoS verb, permits quotative inversion (unaccusative) -/
def whimper : VerbEntry := .mkRegular {
  form := "whimper"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
  unaccusative := true
  levinClass := some .mannerOfSpeaking }

/-- "snap" — MoS verb, permits quotative inversion (unaccusative) -/
def snap : VerbEntry := .mkRegular {
  form := "snap"
  speechActVerb := true
  complementType := .finiteClause
  vendlerClass := some .activity
  subjectTheta := some .theme
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
  subjectTheta := some .agent
  passivizable := false
  levinClass := some .mannerOfSpeaking

/-- "talk" — agentive communication verb, blocks quotative inversion (unergative) -/
def talk : VerbEntry := .mkRegular {
  form := "talk"
  speechActVerb := true
  complementType := .none
  vendlerClass := some .activity
  subjectTheta := some .agent
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
  subjectTheta := some .agent
  takesQuestionBase := true
  levinClass := some .search }

/-- "depend_on" — rogative, embeds interrogatives only (Dayal 2025: rogativeCP) -/
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
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
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
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true
  senseTag := .rogative

-- ════════════════════════════════════════════════════
-- § Verb Entries — Occasion Verbs (Solstad & Bott 2024)
-- ════════════════════════════════════════════════════

/-! Occasion verbs presuppose a prior occasioning eventuality and have
    experiencer (agent-evocator) subjects. They pattern with AgExp verbs
    for implicit causality bias (Solstad & Bott 2024).

    "manage" has two entries: `manage` (`.default`, agentive subject — traditional
    implicative analysis) and `manage_occasion` (`.occasion`, experiencer subject —
    Solstad & Bott's agent-evocator analysis). This mirrors Kim's (2024) observation
    that the same verb can project different effective argument structures
    depending on the interpretive context. -/

/-- "manage" occasion sense — agent-evocator subject (Solstad & Bott 2024).
    Same implicative semantics as `manage`, but subject is experiencer
    (sentience + independent existence, no entailed volition/causation).
    The do-test passes pragmatically because the complement denotes a
    volitional action, not because the matrix verb entails agentivity. -/
def manage_occasion : VerbEntry := .mkRegular {
  form := "manage"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  implicativeBuilder := some .positive
  presupType := some .softTrigger
  senseTag := .occasion }

/-- "dare" — occasion verb: presupposes intimidating circumstance -/
def dare : VerbEntry := .mkRegular {
  form := "dare"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger }

/-- "bother" — occasion verb: presupposes effort/inconvenience -/
def bother : VerbEntry := .mkRegular {
  form := "bother"
  complementType := .infinitival
  vendlerClass := some .achievement
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger }

/-- "hesitate" — occasion verb: presupposes reluctance/risk -/
def hesitate : VerbEntry := .mkRegular {
  form := "hesitate"
  complementType := .infinitival
  vendlerClass := some .activity
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  presupType := some .softTrigger }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Agent-Experiencer (Solstad & Bott 2024)
-- ════════════════════════════════════════════════════

/-! Levin (1993) class 31.2 (admire). Subject = experiencer, object = stimulus.
    NP1 (subject) IC bias. -/

/-- "enjoy" — AgExp verb (experiencer-subject) -/
def enjoy : VerbEntry := .mkRegular {
  form := "enjoy"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "like" — AgExp verb (experiencer-subject) -/
def like : VerbEntry := .mkRegular {
  form := "like"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "love" — AgExp verb (experiencer-subject) -/
def love : VerbEntry := .mkRegular {
  form := "love"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "hate" — AgExp verb (experiencer-subject) -/
def hate : VerbEntry := .mkRegular {
  form := "hate"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "admire" — AgExp verb (experiencer-subject) -/
def admire : VerbEntry := .mkRegular {
  form := "admire"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "envy" — AgExp verb (experiencer-subject) -/
def envy : VerbEntry := .mkRegular {
  form := "envy"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "respect" — AgExp verb (experiencer-subject) -/
def respect : VerbEntry := .mkRegular {
  form := "respect"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "value" — AgExp verb (experiencer-subject) -/
def value : VerbEntry := .mkRegular {
  form := "value"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .admire }

/-- "fear" (NP complement) — Class I psych verb (B&R *temere*).
    "John fears snakes." Experiencer subject, stimulus object.
    Note: `fear` (attitude verb, clausal complement) is defined separately. -/
def fear_np : VerbEntry := .mkRegular {
  form := "fear"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  levinClass := some .admire }

/-- "dread" (NP complement) — Class I psych verb.
    "John dreads exams." Note: `dread` (attitude, clausal) defined separately. -/
def dread_np : VerbEntry := .mkRegular {
  form := "dread"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  levinClass := some .admire }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Stimulus-Experiencer (Solstad & Bott 2024)
-- ════════════════════════════════════════════════════

/-! Levin (1993) class 31.1 (amuse). Subject = stimulus, object = experiencer.
    NP2 (object) IC bias. -/

/-- "frighten" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def frighten : VerbEntry := .mkRegular {
  form := "frighten"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "amuse" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def amuse : VerbEntry := .mkRegular {
  form := "amuse"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "fascinate" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def fascinate : VerbEntry := .mkRegular {
  form := "fascinate"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "irritate" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def irritate : VerbEntry := .mkRegular {
  form := "irritate"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "annoy" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def annoy : VerbEntry := .mkRegular {
  form := "annoy"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "bore" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def bore : VerbEntry := .mkRegular {
  form := "bore"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "charm" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def charm : VerbEntry := .mkRegular {
  form := "charm"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "impress" — StimExp verb (stimulus-subject, eventive: Kim 2024 UPH) -/
def impress : VerbEntry := .mkRegular {
  form := "impress"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "concern" — stative Class II psych verb (Kim 2024 UPH, internal cause) -/
def concern : VerbEntry := .mkRegular {
  form := "concern"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "interest" — stative Class II psych verb (Kim 2024 UPH, internal cause) -/
def interest : VerbEntry := .mkRegular {
  form := "interest"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "surprise" — eventive Class II (Levin 31.1). "The news surprised John." -/
def surprise : VerbEntry := .mkRegular {
  form := "surprise"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "scare" — eventive Class II (Levin 31.1). "The noise scared John." -/
def scare : VerbEntry := .mkRegular {
  form := "scare"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "delight" — eventive Class II (Levin 31.1). "The gift delighted Mary." -/
def delight : VerbEntry := .mkRegular {
  form := "delight"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "embarrass" — eventive Class II (Levin 31.1). "The remark embarrassed John." -/
def embarrass : VerbEntry := .mkRegular {
  form := "embarrass"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "upset" — eventive Class II (Levin 31.1). "The news upset Mary." -/
def upset_psych : VerbEntry := .mkRegular {
  form := "upset"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "disgust" — eventive Class II (Levin 31.1). "The smell disgusted John." -/
def disgust : VerbEntry := .mkRegular {
  form := "disgust"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "shock" — eventive Class II (Levin 31.1). "The revelation shocked everyone." -/
def shock : VerbEntry := .mkRegular {
  form := "shock"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "confuse" — eventive Class II (Levin 31.1). "The instructions confused John." -/
def confuse : VerbEntry := .mkRegular {
  form := "confuse"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "disappoint" — eventive Class II (Levin 31.1). "The result disappointed Mary." -/
def disappoint : VerbEntry := .mkRegular {
  form := "disappoint"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "worry" (eventive) — Class II, external cause. "The noise worried John."
    Note: `worry` (attitude, clausal) defined separately. -/
def worry_eventive : VerbEntry := .mkRegular {
  form := "worry"
  complementType := .np
  vendlerClass := some .accomplishment
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .external
  levinClass := some .amuse }

/-- "worry" (stative) — Class II, internal cause. "The situation worries John."
    Kim (2024) UPH: same theta grid as worry_eventive, different causal source. -/
def worry_stative : VerbEntry := .mkRegular {
  form := "worry"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "please" — stative Class II (Kim 2024 UPH, internal cause).
    "The idea pleases John." Related to B&R Class III It. *piacere*. -/
def please_psych : VerbEntry := .mkRegular {
  form := "please"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "trouble" — stative Class II (Kim 2024 UPH, internal cause).
    "The thought troubles John." -/
def trouble : VerbEntry := .mkRegular {
  form := "trouble"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

/-- "puzzle" — stative Class II (Kim 2024 UPH, internal cause).
    "The problem puzzles John." -/
def puzzle : VerbEntry := .mkRegular {
  form := "puzzle"
  complementType := .np
  vendlerClass := some .state
  subjectTheta := some .stimulus
  objectTheta := some .experiencer
  causalSource := some .internal
  opaqueContext := true
  levinClass := some .amuse }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Agent-Patient (Solstad & Bott 2024)
-- ════════════════════════════════════════════════════

/-! Agent-patient verbs with full agentive subjects. NP1 IC bias (default).
    "kick" already defined above. -/

/-- "chase" — AgPat verb (Levin 51.6) -/
def chase : VerbEntry := .mkRegular {
  form := "chase"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  levinClass := some .hit

/-- "push" — AgPat verb (Levin 12) -/
def push : VerbEntry := .mkRegular {
  form := "push"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pushPull }

/-- "pull" — AgPat verb (Levin 12) -/
def pull : VerbEntry := .mkRegular {
  form := "pull"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pushPull }

/-- "carry" — AgPat verb (Levin 11.4) -/
def carry : VerbEntry where
  form := "carry"
  form3sg := "carries"
  formPast := "carried"
  formPastPart := "carried"
  formPresPart := "carrying"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .carry

/-- "call" — AgPat verb (communication + agent-patient frame) -/
def call : VerbEntry := .mkRegular {
  form := "call"
  complementType := .np
  vendlerClass := some .activity
  subjectTheta := some .agent
  objectTheta := some .patient }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Putting (§ 9)
-- ════════════════════════════════════════════════════

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : VerbEntry := .mkRegular {
  form := "place"
  complementType := .np_pp
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .achievement
  levinClass := some .put }

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : VerbEntry := .mkRegular {
  form := "pour"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .pour }

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : VerbEntry := .mkRegular {
  form := "spray"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .sprayLoad }

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : VerbEntry := .mkRegular {
  form := "load"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .remove }

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : VerbEntry := .mkRegular {
  form := "clean"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .steal

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Sending and Carrying (§ 11)
-- ════════════════════════════════════════════════════

/-- "send" — Levin 11.1 Send verbs. -/
def send : VerbEntry where
  form := "send"
  form3sg := "sends"
  formPast := "sent"
  formPastPart := "sent"
  formPresPart := "sending"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  levinClass := some .contribute }

/-- "obtain" — Levin 13.5 Get verbs. -/
def obtain : VerbEntry := .mkRegular {
  form := "obtain"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  levinClass := some .getObtain }

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : VerbEntry := .mkRegular {
  form := "trade"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .achievement
  levinClass := some .exchange }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Learn, Hold, Conceal (§ 14–16)
-- ════════════════════════════════════════════════════

/-- "learn" — Levin 14 Learn verbs. -/
def learn : VerbEntry := .mkRegular {
  form := "learn"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  levinClass := some .conceal

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Throwing (§ 17)
-- ════════════════════════════════════════════════════

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. -/
def throw : VerbEntry where
  form := "throw"
  form3sg := "throws"
  formPast := "threw"
  formPastPart := "thrown"
  formPresPart := "throwing"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .achievement
  levinClass := some .throw

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Contact (§ 19–20)
-- ════════════════════════════════════════════════════

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : VerbEntry := .mkRegular {
  form := "poke"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .achievement
  levinClass := some .poke }

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : VerbEntry := .mkRegular {
  form := "touch"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .achievement
  levinClass := some .touch }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Cutting (§ 21)
-- ════════════════════════════════════════════════════

/-- "cut" — Levin 21.1 Cut verbs. Incremental by length of cut. -/
def cut : VerbEntry where
  form := "cut"
  form3sg := "cuts"
  formPast := "cut"
  formPastPart := "cut"
  formPresPart := "cutting"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .cut

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : VerbEntry where
  form := "chop"
  form3sg := "chops"
  formPast := "chopped"
  formPastPart := "chopped"
  formPresPart := "chopping"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .mix }

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : VerbEntry := .mkRegular {
  form := "separate"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .separate }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Coloring and Image Creation (§ 24–25)
-- ════════════════════════════════════════════════════

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : VerbEntry := .mkRegular {
  form := "paint"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  verbIncClass := some .sinc
  levinClass := some .grow

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : VerbEntry := .mkRegular {
  form := "perform"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .accomplishment
  levinClass := some .performance }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Predicative Complements (§ 29)
-- ════════════════════════════════════════════════════

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : VerbEntry := .mkRegular {
  form := "appoint"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .achievement
  levinClass := some .appoint }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Perception (§ 30)
-- ════════════════════════════════════════════════════

/-- "hear" — Levin 30.1 See verbs. Stative perception. -/
def hear : VerbEntry where
  form := "hear"
  form3sg := "hears"
  formPast := "heard"
  formPastPart := "heard"
  formPresPart := "hearing"
  complementType := .np
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  vendlerClass := some .state
  levinClass := some .see

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Judgment and Assessment (§ 33–34)
-- ════════════════════════════════════════════════════

/-- "blame" — Levin 33 Judgment verbs. -/
def blame : VerbEntry := .mkRegular {
  form := "blame"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  verbIncClass := some .cumOnly
  levinClass := some .judgment }

/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : VerbEntry := .mkRegular {
  form := "evaluate"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .achievement
  levinClass := some .socialInteraction

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Animal Sounds (§ 38)
-- ════════════════════════════════════════════════════

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : VerbEntry := .mkRegular {
  form := "bark"
  complementType := .none
  subjectTheta := some .agent
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
  subjectTheta := some .agent
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .bodyProcess }

/-- "cough" — Levin 40.1 Body Process verbs. -/
def cough : VerbEntry := .mkRegular {
  form := "cough"
  complementType := .none
  subjectTheta := some .agent
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .bodyProcess }

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : VerbEntry := .mkRegular {
  form := "flinch"
  complementType := .none
  subjectTheta := some .experiencer
  passivizable := false
  vendlerClass := some .achievement
  levinClass := some .flinch }

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : VerbEntry := .mkRegular {
  form := "dress"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  levinClass := some .dress }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Killing (§ 42)
-- ════════════════════════════════════════════════════

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : VerbEntry := .mkRegular {
  form := "drown"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  causativeBuilder := some .make
  levinClass := some .poison }

-- ════════════════════════════════════════════════════
-- § Levin Class Expansion — Emission (§ 43)
-- ════════════════════════════════════════════════════

/-- "glow" — Levin 43.1 Light Emission verbs. -/
def glow : VerbEntry := .mkRegular {
  form := "glow"
  complementType := .none
  subjectTheta := some .theme
  passivizable := false
  vendlerClass := some .state
  unaccusative := true
  levinClass := some .lightEmission }

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : VerbEntry := .mkRegular {
  form := "buzz"
  complementType := .none
  subjectTheta := some .theme
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
  subjectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "curvature" }
  causativeBuilder := some .make
  levinClass := some .bend

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : VerbEntry := .mkRegular {
  form := "boil"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .accomplishment
  degreeAchievementScale := some {
    scaleBoundedness := .closed, dimension := "temperature",
    baseAdjective := some "hot" }
  causativeBuilder := some .make
  levinClass := some .cooking }

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : VerbEntry := .mkRegular {
  form := "rust"
  complementType := .none
  subjectTheta := some .theme
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
  subjectTheta := some .agent
  objectTheta := some .patient
  vendlerClass := some .activity
  degreeAchievementScale := some {
    scaleBoundedness := .open_, dimension := "quantity" }
  levinClass := some .calibratableCoS }

-- ════════════════════════════════════════════════════
-- § Degree Achievement Verb Pairs (Kennedy & Levin 2007)
-- ════════════════════════════════════════════════════

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : VerbEntry := .mkRegular {
  form := "straighten"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .agent
  objectTheta := some .patient
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
  subjectTheta := some .theme
  passivizable := false
  vendlerClass := some .state
  unaccusative := true
  levinClass := some .exist }

/-- "appear" — Levin 48.1 Appear verbs. Punctual emergence. -/
def appear : VerbEntry := .mkRegular {
  form := "appear"
  complementType := .none
  subjectTheta := some .theme
  passivizable := false
  vendlerClass := some .achievement
  unaccusative := true
  levinClass := some .appear }

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : VerbEntry := .mkRegular {
  form := "fidget"
  complementType := .none
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
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
  subjectTheta := some .agent
  objectTheta := some .theme
  vendlerClass := some .state
  levinClass := some .avoid }

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : VerbEntry := .mkRegular {
  form := "linger"
  complementType := .none
  subjectTheta := some .agent
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .linger }

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : VerbEntry := .mkRegular {
  form := "rush"
  complementType := .none
  subjectTheta := some .agent
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
  subjectTheta := none
  passivizable := false
  vendlerClass := some .activity
  levinClass := some .weather }

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
  manage, fail, try_, persuade, promise, remember, forget,
  -- Doxastic Attitude
  believe, think,
  -- Preferential Attitude (Qing et al. 2025)
  want, hope, expect, wish,
  fear, dread,
  worry,
  -- Raising
  seem,
  -- Causative (Nadathur & Lauer 2020 + Wolff 2003)
  cause,
  make,
  let_, have_caus, get_caus, force,
  -- Lexical causatives (Martin, Rose & Nichols 2025)
  kill, break_, tear_, burn, destroy, melt,
  activate, affect, change, damage, eliminate, hurt, restore, trigger,
  bury, drop, lift, lock, shut, spread, stretch, switch,
  -- Communication
  say, tell, claim,
  -- Manner of Speaking (Storment 2026)
  whisper, murmur, shout, cry, scream, speak, talk,
  -- Question-embedding (Dayal 2025)
  wonder, ask, investigate, depend_on,
  -- Factive question-embedding senses
  remember_rog, forget_rog,
  -- Occasion Verbs (Solstad & Bott 2024)
  manage_occasion, dare, bother, hesitate,
  -- Agent-Experiencer (Solstad & Bott 2024)
  enjoy, like, love, hate, admire, envy, respect, value,
  -- Stimulus-Experiencer (Solstad & Bott 2024)
  frighten, amuse, fascinate, irritate, annoy, bore, charm, impress,
  -- Stative Class II (Kim 2024 UPH)
  concern, interest,
  -- Agent-Patient (Solstad & Bott 2024)
  chase, hit, push, pull, carry, drag, call,
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
  -- Degree Achievement Pairs (Kennedy & Levin 2007)
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

/-! These verify that the Fragment's causative annotations are consistent with
the formal semantics in `NadathurLauer2020`. -/

open NadathurLauer2020.Builder (CausativeBuilder)
open NadathurLauer2020.Sufficiency (makeSem)
open NadathurLauer2020.Necessity (causeSem)

/-- "make" uses sufficiency semantics. -/
theorem make_semantics :
    make.causativeBuilder.map CausativeBuilder.toSemantics = some makeSem := rfl

/-- "cause" uses necessity semantics. -/
theorem cause_semantics :
    cause.causativeBuilder.map CausativeBuilder.toSemantics = some causeSem := rfl

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
    make.causativeBuilder = have_caus.causativeBuilder ∧
    make.causativeBuilder = get_caus.causativeBuilder := ⟨rfl, rfl⟩

/-- "force" is coercive — derived from its builder. -/
theorem force_is_coercive :
    force.causativeBuilder.map (·.isCoercive) = some true := rfl

/-- "let" is permissive — derived from its builder. -/
theorem let_is_permissive :
    let_.causativeBuilder.map (·.isPermissive) = some true := rfl

/-- All sufficiency-asserting causatives share the same truth conditions. -/
theorem sufficiency_verbs_share_truth_conditions :
    make.causativeBuilder.map CausativeBuilder.toSemantics =
    force.causativeBuilder.map CausativeBuilder.toSemantics ∧
    make.causativeBuilder.map CausativeBuilder.toSemantics =
    let_.causativeBuilder.map CausativeBuilder.toSemantics ∧
    make.causativeBuilder.map CausativeBuilder.toSemantics =
    have_caus.causativeBuilder.map CausativeBuilder.toSemantics ∧
    make.causativeBuilder.map CausativeBuilder.toSemantics =
    get_caus.causativeBuilder.map CausativeBuilder.toSemantics :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- make, force, and let have different builders despite shared truth conditions. -/
theorem causative_builders_distinguished :
    make.causativeBuilder ≠ force.causativeBuilder ∧
    make.causativeBuilder ≠ let_.causativeBuilder ∧
    force.causativeBuilder ≠ let_.causativeBuilder := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Lexical causative theorems (Martin, Rose & Nichols 2025) -/

/-- All lexical causatives use the `.make` builder. -/
theorem lexical_causatives_use_make :
    kill.causativeBuilder = some .make ∧
    break_.causativeBuilder = some .make ∧
    burn.causativeBuilder = some .make ∧
    destroy.causativeBuilder = some .make ∧
    melt.causativeBuilder = some .make := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Lexical causatives all assert sufficiency — like periphrastic "make". -/
theorem lexical_causatives_assert_sufficiency :
    kill.toVerbCore.assertsSufficiency = true ∧
    break_.toVerbCore.assertsSufficiency = true ∧
    burn.toVerbCore.assertsSufficiency = true ∧
    destroy.toVerbCore.assertsSufficiency = true ∧
    melt.toVerbCore.assertsSufficiency = true := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

/-- Lexical causatives share truth conditions with periphrastic "make". -/
theorem lexical_causatives_match_make :
    kill.causativeBuilder.map CausativeBuilder.toSemantics =
    make.causativeBuilder.map CausativeBuilder.toSemantics ∧
    break_.causativeBuilder.map CausativeBuilder.toSemantics =
    make.causativeBuilder.map CausativeBuilder.toSemantics := ⟨rfl, rfl⟩

/-- Lexical causatives differ from periphrastic "cause" in truth conditions. -/
theorem lexical_causatives_differ_from_cause :
    kill.causativeBuilder ≠ cause.causativeBuilder ∧
    break_.causativeBuilder ≠ cause.causativeBuilder := by
  constructor <;> decide

-- ════════════════════════════════════════════════════
-- § Implicative Grounding Theorems
-- ════════════════════════════════════════════════════

open Nadathur2023.Implicative (ImplicativeBuilder manageSem failSem)

/-- "manage" uses positive implicative semantics (`manageSem`). -/
theorem manage_semantics_implicative :
    manage.implicativeBuilder.map ImplicativeBuilder.toSemantics =
      some manageSem := rfl

/-- "fail" uses negative implicative semantics (`failSem`). -/
theorem fail_semantics_implicative :
    fail.implicativeBuilder.map ImplicativeBuilder.toSemantics =
      some failSem := rfl

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

end Fragments.English.Predicates.Verbal
