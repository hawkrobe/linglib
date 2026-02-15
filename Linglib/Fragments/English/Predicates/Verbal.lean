import Linglib.Core.Verbs
import Linglib.Core.Morphology.MorphRule

/-! # Verbal Predicate Lexicon Fragment

English verb lexical entries with morphology, argument structure, semantic class,
and links to compositional semantics (CoS, attitudes, causatives).

Semantic types (`VerbClass`, `ComplementType`, `AttitudeBuilder`, etc.) and the
cross-linguistic `VerbCore` structure live in `Core/Verbs.lean`. This file
defines `VerbEntry extends VerbCore` with English-specific inflectional fields
and provides smart constructors for regular verbs.
-/

namespace Fragments.English.Predicates.Verbal

-- Re-export Core.Verbs types so downstream files that open this namespace
-- (e.g., `open Fragments.English.Predicates.Verbal (VerbClass ComplementType ...)`)
-- continue to find them.
export Core.Verbs (PreferentialBuilder AttitudeBuilder VerbClass PresupTriggerType
  ComplementType ControlType VerbCore complementToValence)

open Core.Verbs
open NadathurLauer2020.Builder (CausativeBuilder)
open Nadathur2023.Implicative (ImplicativeBuilder)

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
      form := "kick", complementType := .np, verbClass := .simple
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
  verbClass := .simple

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
  verbClass := .simple

/-- "arrive" — unaccusative intransitive -/
def arrive : VerbEntry := .mkRegular {
  form := "arrive"
  complementType := .none
  subjectTheta := some .theme  -- Underlying object
  unaccusative := true
  passivizable := false
  verbClass := .simple }

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
  verbClass := .simple

/-- "kick" — transitive -/
def kick : VerbEntry := .mkRegular {
  form := "kick"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .simple }

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
  verbClass := .simple

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
  verbClass := .simple

/-- "weigh" — measure predicate selecting for mass/weight (Bale & Schwarz 2026). -/
def weigh : VerbEntry := .mkRegular {
  form := "weigh"
  complementType := .np
  subjectTheta := some .theme
  objectTheta := some .theme
  verbClass := .simple
  selectsDimension := some .mass }

/-- "cover" — motion/extent predicate selecting for distance (Bale & Schwarz 2026). -/
def cover : VerbEntry := .mkRegular {
  form := "cover"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  verbClass := .simple
  selectsDimension := some .distance }

/-- "measure" — general measurement predicate. -/
def measure : VerbEntry := .mkRegular {
  form := "measure"
  complementType := .np
  subjectTheta := some .theme
  objectTheta := some .theme
  verbClass := .simple }

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
  verbClass := .perception
  factivePresup := true

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
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true

/-- "regret" — factive, presupposes complement is true -/
def regret : VerbEntry where
  form := "regret"
  form3sg := "regrets"
  formPast := "regretted"
  formPastPart := "regretted"
  formPresPart := "regretting"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true

/-- "realize" — factive, presupposes complement is true -/
def realize : VerbEntry := .mkRegular {
  form := "realize"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true }

/-- "discover" — semifactive, weaker projection -/
def discover : VerbEntry := .mkRegular {
  form := "discover"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .semifactive
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true }

/-- "notice" — semifactive -/
def notice : VerbEntry := .mkRegular {
  form := "notice"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .semifactive
  presupType := some .softTrigger
  factivePresup := true }

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
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .cessation

/-- "quit" — CoS cessation -/
def quit : VerbEntry where
  form := "quit"
  form3sg := "quits"
  formPast := "quit"
  formPastPart := "quit"
  formPresPart := "quitting"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .cessation

/-- "start" — CoS inception, presupposes activity wasn't happening -/
def start : VerbEntry := .mkRegular {
  form := "start"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .inception }

/-- "begin" — CoS inception -/
def begin_ : VerbEntry where
  form := "begin"
  form3sg := "begins"
  formPast := "began"
  formPastPart := "begun"
  formPresPart := "beginning"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .inception

/-- "continue" — CoS continuation, presupposes activity was happening -/
def continue_ : VerbEntry := .mkRegular {
  form := "continue"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .continuation }

/-- "keep" — CoS continuation -/
def keep : VerbEntry where
  form := "keep"
  form3sg := "keeps"
  formPast := "kept"
  formPastPart := "kept"
  formPresPart := "keeping"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .continuation

-- ════════════════════════════════════════════════════
-- § Verb Entries — Implicative / Control
-- ════════════════════════════════════════════════════

/-- "manage" — positive implicative: "managed to VP" entails "VP" -/
def manage : VerbEntry := .mkRegular {
  form := "manage"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeBuilder := some .positive }

/-- "fail" — negative implicative: "failed to VP" entails "not VP" -/
def fail : VerbEntry := .mkRegular {
  form := "fail"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeBuilder := some .negative }

/-- "try" — subject control, no entailment -/
def try_ : VerbEntry where
  form := "try"
  form3sg := "tries"
  formPast := "tried"
  formPastPart := "tried"
  formPresPart := "trying"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .simple

/-- "persuade" — object control: "persuade X to VP" (X = agent of VP) -/
def persuade : VerbEntry := .mkRegular {
  form := "persuade"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .experiencer
  controlType := .objectControl
  verbClass := .simple }

/-- "promise" — subject control with object: "promise X to VP" -/
def promise : VerbEntry := .mkRegular {
  form := "promise"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .goal
  controlType := .subjectControl
  verbClass := .simple }

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : VerbEntry := .mkRegular {
  form := "remember"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeBuilder := some .positive }

/-- "forget" — negative implicative with infinitival -/
def forget : VerbEntry where
  form := "forget"
  form3sg := "forgets"
  formPast := "forgot"
  formPastPart := "forgotten"
  formPresPart := "forgetting"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeBuilder := some .negative

-- ════════════════════════════════════════════════════
-- § Verb Entries — Doxastic Attitude
-- ════════════════════════════════════════════════════

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : VerbEntry := .mkRegular {
  form := "believe"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.doxastic .nonVeridical) }

/-- "think" — doxastic attitude verb -/
def think : VerbEntry where
  form := "think"
  form3sg := "thinks"
  formPast := "thought"
  formPastPart := "thought"
  formPresPart := "thinking"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.doxastic .nonVeridical)

-- ════════════════════════════════════════════════════
-- § Verb Entries — Preferential Attitude
-- ════════════════════════════════════════════════════

/-- "want" — preferential attitude verb with infinitival complement -/
def want : VerbEntry := .mkRegular {
  form := "want"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive)) }

/-- "hope" — preferential attitude verb (Class 3: anti-rogative) -/
def hope : VerbEntry := .mkRegular {
  form := "hope"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive)) }

/-- "expect" — preferential attitude verb (Class 3: anti-rogative) -/
def expect : VerbEntry := .mkRegular {
  form := "expect"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive)) }

/-- "wish" — preferential attitude verb (Class 3: anti-rogative) -/
def wish : VerbEntry where
  form := "wish"
  form3sg := "wishes"
  formPast := "wished"
  formPastPart := "wished"
  formPresPart := "wishing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- "fear" — preferential attitude verb (Class 2: takes questions) -/
def fear : VerbEntry := .mkRegular {
  form := "fear"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative)) }

/-- "dread" — preferential attitude verb (Class 2: takes questions) -/
def dread : VerbEntry := .mkRegular {
  form := "dread"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential (.degreeComparison .negative)) }

/-- "worry" — preferential attitude verb (Class 1: takes questions, non-C-distributive) -/
def worry : VerbEntry where
  form := "worry"
  form3sg := "worries"
  formPast := "worried"
  formPastPart := "worried"
  formPresPart := "worrying"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  attitudeBuilder := some (.preferential .uncertaintyBased)

-- ════════════════════════════════════════════════════
-- § Verb Entries — Raising
-- ════════════════════════════════════════════════════

/-- "seem" — raising verb (no theta role for subject) -/
def seem : VerbEntry := .mkRegular {
  form := "seem"
  complementType := .infinitival
  subjectTheta := none
  controlType := .raising
  passivizable := false
  verbClass := .simple }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Causative (Periphrastic)
-- ════════════════════════════════════════════════════

/-- "cause" — counterfactual dependence (necessity semantics) -/
def cause : VerbEntry := .mkRegular {
  form := "cause"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .cause }

/-- "make" — direct sufficient guarantee -/
def make : VerbEntry where
  form := "make"
  form3sg := "makes"
  formPast := "made"
  formPastPart := "made"
  formPresPart := "making"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .make

/-- "let" — permissive causative (barrier removal) -/
def let_ : VerbEntry where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .enable

/-- "have" — causative use (directive causation) -/
def have_caus : VerbEntry where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  complementType := .smallClause
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
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
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .make
  senseTag := .causative

/-- "force" — coercive causative (overcome resistance) -/
def force : VerbEntry := .mkRegular {
  form := "force"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
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
  verbClass := .causative
  causativeBuilder := some .make }

/-- "break" — thick lexical causative (manner verb, Embick 2009 break-class). -/
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
  verbClass := .causative
  causativeBuilder := some .make

/-- "burn" — thick lexical causative (manner = by fire/heat). -/
def burn : VerbEntry := .mkRegular {
  form := "burn"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .causative
  causativeBuilder := some .make }

/-- "destroy" — thin lexical causative (result-only, no manner). -/
def destroy : VerbEntry := .mkRegular {
  form := "destroy"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .causative
  causativeBuilder := some .make }

/-- "melt" — thick lexical causative (manner = by heat). -/
def melt : VerbEntry := .mkRegular {
  form := "melt"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .causative
  causativeBuilder := some .make }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Other
-- ════════════════════════════════════════════════════

/-- "devour" — transitive, no presupposition -/
def devour : VerbEntry := .mkRegular {
  form := "devour"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .simple }

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
  verbClass := .simple

/-- "sweep" — motion + sustained contact, variable agentivity (default sense). -/
def sweep : VerbEntry where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  complementType := .np
  subjectTheta := none
  objectTheta := some .theme
  verbClass := .simple
  passivizable := true

/-- "sweep" instrument sense — obligatorily agentive, broom lexicalized. -/
def sweep_instr : VerbEntry where
  form := "sweep"
  form3sg := "sweeps"
  formPast := "swept"
  formPastPart := "swept"
  formPresPart := "sweeping"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .theme
  verbClass := .simple
  passivizable := true
  senseTag := .instrumental

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
  verbClass := .communication
  complementType := .finiteClause

/-- "tell" — communication verb with recipient -/
def tell : VerbEntry where
  form := "tell"
  form3sg := "tells"
  formPast := "told"
  formPastPart := "told"
  formPresPart := "telling"
  verbClass := .communication
  complementType := .finiteClause

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : VerbEntry := .mkRegular {
  form := "claim"
  verbClass := .communication
  complementType := .finiteClause }

-- ════════════════════════════════════════════════════
-- § Verb Entries — Question-Embedding
-- ════════════════════════════════════════════════════

/-- "wonder" — embeds questions only -/
def wonder : VerbEntry := .mkRegular {
  form := "wonder"
  verbClass := .attitude
  complementType := .question
  takesQuestionBase := true
  opaqueContext := true }

/-- "ask" — embeds questions -/
def ask : VerbEntry := .mkRegular {
  form := "ask"
  verbClass := .communication
  complementType := .question
  takesQuestionBase := true }

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : VerbEntry := .mkRegular {
  form := "investigate"
  verbClass := .simple
  complementType := .question
  subjectTheta := some .agent
  takesQuestionBase := true }

/-- "depend_on" — rogative, embeds interrogatives only (Dayal 2025: rogativeCP) -/
def depend_on : VerbEntry where
  form := "depend on"
  form3sg := "depends on"
  formPast := "depended on"
  formPastPart := "depended on"
  formPresPart := "depending on"
  verbClass := .simple
  complementType := .question
  takesQuestionBase := true

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : VerbEntry := .mkRegular {
  form := "remember"
  verbClass := .factive
  complementType := .finiteClause
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
  verbClass := .factive
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true
  senseTag := .rogative

-- ════════════════════════════════════════════════════
-- § Verb List and Lookup
-- ════════════════════════════════════════════════════

/-- Get all verb entries as a list (for enumeration). -/
def allVerbs : List VerbEntry := [
  -- Simple
  sleep, run, arrive, eat, kick, give, put, see, devour, read, sweep, sweep_instr,
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
  kill, break_, burn, destroy, melt,
  -- Communication
  say, tell, claim,
  -- Question-embedding (Dayal 2025)
  wonder, ask, investigate, depend_on,
  -- Factive question-embedding senses
  remember_rog, forget_rog
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
    }
  }

/-- Convert a verb entry to a `Word` in base/plural present form. -/
def VerbEntry.toWordPl (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , number := some .pl
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
    `IntensionalSemantics`. The `isVacuous := true` flags make
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
