import Linglib.Core.Basic
import Linglib.Core.Presupposition
import Linglib.Theories.TruthConditional.Verb.ChangeOfState.Theory
import Linglib.Theories.IntensionalSemantics.Attitude.Doxastic
import Linglib.Theories.IntensionalSemantics.Attitude.Preferential
import Linglib.Theories.IntensionalSemantics.Causative.Basic

/-! # Verbal Predicate Lexicon Fragment

Verb lexical entries with morphology, argument structure, semantic class,
and links to compositional semantics (CoS, attitudes, causatives).
-/

namespace Fragments.English.Predicates.Verbal

open Core.Presupposition
open TruthConditional.Verb.ChangeOfState
open IntensionalSemantics.Attitude.Doxastic (Veridicality)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass PreferentialPredicate)

/--
Which Montague predicate builder this verb uses.

This links the Fragment entry to the compositional semantics in
`IntensionalSemantics.Attitude.Preferential`. Properties like C-distributivity
are DERIVED from the builder via theorems, not stipulated.

- `degreeComparison`: Uses `mkDegreeComparisonPredicate` → C-distributive (PROVED)
- `uncertaintyBased`: Uses `worry` constructor → NOT C-distributive (PROVED)
- `relevanceBased`: Uses `qidai` constructor → NOT C-distributive

The connection to Montague is:
- `degreeComparison .positive` → `Preferential.hope`, `Preferential.expect`, etc.
- `degreeComparison .negative` → `Preferential.fear`, `Preferential.dread`
- `uncertaintyBased` → `Preferential.worry`
- `relevanceBased .positive` → `Preferential.qidai`
-/
inductive PreferentialBuilder where
  /-- Degree comparison semantics: ⟦x V Q⟧ = ∃p ∈ Q. μ(x,p) > θ. C-distributive. -/
  | degreeComparison (valence : AttitudeValence)
  /-- Uncertainty-based semantics (worry): involves global uncertainty. NOT C-distributive. -/
  | uncertaintyBased
  /-- Relevance-based semantics (qidai, care): involves resolution. NOT C-distributive. -/
  | relevanceBased (valence : AttitudeValence)
  deriving DecidableEq, Repr, BEq

/-- Get the valence from the builder -/
def PreferentialBuilder.valence : PreferentialBuilder → AttitudeValence
  | .degreeComparison v => v
  | .uncertaintyBased => .negative  -- worry is negative
  | .relevanceBased v => v

/--
Unified builder for all attitude verbs, covering both doxastic (believe, know)
and preferential (hope, fear) attitudes.

This is the **minimal basis** from which theoretical properties are derived:
1. **Doxastic attitudes**: Use accessibility relations (Hintikka semantics)
2. **Preferential attitudes**: Use degree/uncertainty semantics (Villalta)

Derived properties (in Theory layer):
- C-distributivity: from PreferentialBuilder structure (Qing et al. 2025)
- NVP class: from C-distributivity + valence
- Parasitic on belief: from being preferential (Maier 2015)
- Presupposition projection: from veridicality + attitude type (Heim 1992)
-/
inductive AttitudeBuilder where
  /-- Doxastic attitude (believe, know, think) with accessibility semantics -/
  | doxastic (veridicality : Veridicality)
  /-- Preferential attitude (hope, fear, worry) with degree/uncertainty semantics -/
  | preferential (builder : PreferentialBuilder)
  deriving DecidableEq, Repr, BEq

/-- Get veridicality from an attitude builder -/
def AttitudeBuilder.veridicality : AttitudeBuilder → Veridicality
  | .doxastic v => v
  | .preferential _ => .nonVeridical  -- Preferential attitudes are non-veridical

/-- Is this a doxastic attitude? -/
def AttitudeBuilder.isDoxastic : AttitudeBuilder → Bool
  | .doxastic _ => true
  | .preferential _ => false

/-- Is this a preferential attitude? -/
def AttitudeBuilder.isPreferential : AttitudeBuilder → Bool
  | .doxastic _ => false
  | .preferential _ => true

/-- Get the preferential builder if this is a preferential attitude -/
def AttitudeBuilder.getPreferentialBuilder : AttitudeBuilder → Option PreferentialBuilder
  | .doxastic _ => none
  | .preferential b => some b

/-- Get valence for preferential attitudes -/
def AttitudeBuilder.valence : AttitudeBuilder → Option AttitudeValence
  | .doxastic _ => none
  | .preferential b => some b.valence

/--
Semantic class of verb.

This classification determines what semantic machinery is needed:
- Simple verbs just need a standard denotation
- Factives need presupposition projection
- CoS verbs need temporal/change structure
- Attitudes need intensional semantics
- Causatives need causal model semantics (Nadathur & Lauer 2020)
-/
inductive VerbClass where
  | simple          -- sleep, run, eat
  | factive         -- know, regret, realize
  | semifactive     -- discover, notice (weaker projection)
  | changeOfState   -- stop, start, continue
  | implicative     -- manage, fail, remember (to)
  | attitude        -- believe, think, want
  | perception      -- see, hear (ambiguous: factive or not)
  | communication   -- say, tell, claim
  | causative       -- cause, make (Nadathur & Lauer 2020)
  deriving DecidableEq, Repr, BEq

/--
Presupposition trigger type (Tonhauser et al. 2013 classification).

- Hard triggers: Always project (too, again, also)
- Soft triggers: Context-sensitive projection (stop, know)
-/
inductive PresupTriggerType where
  | hardTrigger     -- Projective in all contexts
  | softTrigger     -- Can be locally accommodated
  deriving DecidableEq, Repr, BEq

-- CausativeBuilder is imported from Theories.NadathurLauer2020.Builder
-- (via Causative.Basic). Like PreferentialBuilder for attitude verbs,
-- it links lexical entries to their compositional semantics. Properties
-- like "asserts sufficiency" are DERIVED from the builder via theorems.
open Theories.NadathurLauer2020.Builder (CausativeBuilder)

/--
Complement type that the verb selects.

- Finite: "that" clauses ("John knows that Mary left")
- Infinitival: "to" complements ("John managed to leave")
- Gerund: "-ing" complements ("John stopped smoking")
- NP: Direct object ("John kicked the ball")
- None: Intransitive ("John slept")
-/
inductive ComplementType where
  | none            -- Intransitive
  | np              -- Transitive with NP object
  | np_np           -- Ditransitive: "give X Y"
  | np_pp           -- NP + PP: "put X on Y"
  | finiteClause    -- "that" clause
  | infinitival     -- "to" VP
  | gerund          -- "-ing" VP
  | smallClause     -- "consider X happy"
  | question        -- Embedded question "wonder who"
  deriving DecidableEq, Repr, BEq

/--
Theta roles for argument structure.
-/
inductive ThetaRole where
  | agent       -- Volitional causer (John kicked the ball)
  | patient     -- Affected entity (John kicked the ball)
  | theme       -- Entity in a state/location (The book is on the table)
  | experiencer -- Perceiver/cognizer (John knows that p)
  | goal        -- Recipient/target (John gave Mary a book)
  | source      -- Origin (John came from Paris)
  | instrument  -- Means (John opened the door with a key)
  | stimulus    -- Cause of experience (The noise frightened John)
  deriving DecidableEq, Repr, BEq

/--
Control type for verbs with infinitival complements.
-/
inductive ControlType where
  | subjectControl  -- "John tried to leave" (John = leaver)
  | objectControl   -- "John persuaded Mary to leave" (Mary = leaver)
  | raising         -- "John seems to be happy" (no theta role for matrix subject)
  | none            -- Not applicable
  deriving DecidableEq, Repr, BEq

/--
A complete lexical entry for a verb.

Bundles all information needed for semantic/pragmatic analysis:
- Surface form and basic morphology
- Syntactic selection (complement type, valence)
- Argument structure (theta roles, control)
- Semantic class and presupposition behavior
- Link to compositional semantics (CoS type, factivity, etc.)
-/
structure VerbEntry where
  -- === Morphology ===
  /-- Citation form (infinitive) -/
  form : String
  /-- Third person singular present (for agreement) -/
  form3sg : String
  /-- Past tense form -/
  formPast : String
  /-- Past participle (for passives, perfects) -/
  formPastPart : String
  /-- Present participle / gerund -/
  formPresPart : String

  -- === Argument Structure ===
  /-- What complement does the verb select? -/
  complementType : ComplementType
  /-- Theta role of external argument (subject) -/
  subjectTheta : Option ThetaRole := none
  /-- Theta role of internal argument (object) -/
  objectTheta : Option ThetaRole := none
  /-- Theta role of second internal argument (indirect object) -/
  object2Theta : Option ThetaRole := none
  /-- Control type for infinitival complements -/
  controlType : ControlType := .none
  /-- Is the verb unaccusative? (subject is underlying object) -/
  unaccusative : Bool := false
  /-- Can the verb passivize? -/
  passivizable : Bool := true

  -- === Semantic Class ===
  /-- Semantic verb class -/
  verbClass : VerbClass
  /-- Is the verb a presupposition trigger? -/
  presupType : Option PresupTriggerType := none

  -- === Class-Specific Features ===
  /-- For CoS verbs: which type (cessation, inception, continuation)? -/
  cosType : Option CoSType := none
  /-- For factive verbs: what does it presuppose about its complement? -/
  factivePresup : Bool := false
  /-- For implicative verbs: does success of main verb entail complement? -/
  implicativeEntailment : Option Bool := none
  /-- For causative verbs: which semantic builder (links to compositional semantics). -/
  causativeBuilder : Option CausativeBuilder := none

  -- === Intensionality ===
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false

  -- === Attitude-Specific Properties ===
  /-- Unified attitude builder covering doxastic and preferential attitudes.
      Theoretical properties (C-distributivity, parasitic, etc.) are DERIVED. -/
  attitudeBuilder : Option AttitudeBuilder := none
  /-- For non-preferential question-embedding verbs (know, wonder, ask) -/
  takesQuestionBase : Bool := false
  deriving Repr, BEq

/-- Veridicality is DERIVED from the attitude builder -/
def VerbEntry.veridicality (v : VerbEntry) : Option Veridicality :=
  v.attitudeBuilder.map (·.veridicality)


/-- Is this verb a doxastic attitude? -/
def VerbEntry.isDoxastic (v : VerbEntry) : Bool :=
  v.attitudeBuilder.map (·.isDoxastic) |>.getD false

/-- Is this verb a preferential attitude? -/
def VerbEntry.isPreferential (v : VerbEntry) : Bool :=
  v.attitudeBuilder.map (·.isPreferential) |>.getD false

/-- Valence is DERIVED from the attitude builder (for preferential attitudes) -/
def VerbEntry.preferentialValence (v : VerbEntry) : Option AttitudeValence :=
  v.attitudeBuilder.bind (·.valence)

-- Note: VerbEntry.cDistributive, VerbEntry.nvpClass, and VerbEntry.takesQuestion
-- are derived properties defined in Theories/Montague/Verb/Attitude/BuilderProperties.lean

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
def arrive : VerbEntry where
  form := "arrive"
  form3sg := "arrives"
  formPast := "arrived"
  formPastPart := "arrived"
  formPresPart := "arriving"
  complementType := .none
  subjectTheta := some .theme  -- Underlying object
  unaccusative := true
  passivizable := false
  verbClass := .simple

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
def kick : VerbEntry where
  form := "kick"
  form3sg := "kicks"
  formPast := "kicked"
  formPastPart := "kicked"
  formPresPart := "kicking"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .simple

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

/-- "see" — transitive, can also embed clauses -/
def see : VerbEntry where
  form := "see"
  form3sg := "sees"
  formPast := "saw"
  formPastPart := "seen"
  formPresPart := "seeing"
  complementType := .np  -- Can also take .finiteClause
  subjectTheta := some .experiencer
  objectTheta := some .stimulus
  verbClass := .perception
  factivePresup := true  -- "see that p" presupposes p

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
  takesQuestionBase := true  -- "know who/what/whether"

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
def realize : VerbEntry where
  form := "realize"
  form3sg := "realizes"
  formPast := "realized"
  formPastPart := "realized"
  formPresPart := "realizing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .factive
  presupType := some .softTrigger
  factivePresup := true

/-- "discover" — semifactive, weaker projection -/
def discover : VerbEntry where
  form := "discover"
  form3sg := "discovers"
  formPast := "discovered"
  formPastPart := "discovered"
  formPresPart := "discovering"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .semifactive
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true

/-- "notice" — semifactive -/
def notice : VerbEntry where
  form := "notice"
  form3sg := "notices"
  formPast := "noticed"
  formPastPart := "noticed"
  formPresPart := "noticing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .semifactive
  presupType := some .softTrigger
  factivePresup := true

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
def start : VerbEntry where
  form := "start"
  form3sg := "starts"
  formPast := "started"
  formPastPart := "started"
  formPresPart := "starting"
  complementType := .gerund  -- Can also take .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .inception

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
def continue_ : VerbEntry where
  form := "continue"
  form3sg := "continues"
  formPast := "continued"
  formPastPart := "continued"
  formPresPart := "continuing"
  complementType := .gerund
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .changeOfState
  presupType := some .softTrigger
  cosType := some .continuation

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

/-- "manage" — positive implicative: "managed to VP" entails "VP" -/
def manage : VerbEntry where
  form := "manage"
  form3sg := "manages"
  formPast := "managed"
  formPastPart := "managed"
  formPresPart := "managing"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some true  -- Success entails complement

/-- "fail" — negative implicative: "failed to VP" entails "not VP" -/
def fail : VerbEntry where
  form := "fail"
  form3sg := "fails"
  formPast := "failed"
  formPastPart := "failed"
  formPresPart := "failing"
  complementType := .infinitival
  subjectTheta := some .agent
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some false  -- Success entails NOT complement

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
def persuade : VerbEntry where
  form := "persuade"
  form3sg := "persuades"
  formPast := "persuaded"
  formPastPart := "persuaded"
  formPresPart := "persuading"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .experiencer  -- The persuadee
  controlType := .objectControl
  verbClass := .simple

/-- "promise" — subject control with object: "promise X to VP" (subject = agent of VP) -/
def promise : VerbEntry where
  form := "promise"
  form3sg := "promises"
  formPast := "promised"
  formPastPart := "promised"
  formPresPart := "promising"
  complementType := .infinitival
  subjectTheta := some .agent
  objectTheta := some .goal
  controlType := .subjectControl  -- Unusual: subject control despite object
  verbClass := .simple

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : VerbEntry where
  form := "remember"
  form3sg := "remembers"
  formPast := "remembered"
  formPastPart := "remembered"
  formPresPart := "remembering"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .implicative
  implicativeEntailment := some true
  -- Note: "remember that p" is factive, but "remember to VP" is implicative

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
  implicativeEntailment := some false
  -- Note: "forget that p" is factive

/-- "believe" — doxastic attitude verb, creates opaque context -/
def believe : VerbEntry where
  form := "believe"
  form3sg := "believes"
  formPast := "believed"
  formPastPart := "believed"
  formPresPart := "believing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Doxastic: accessibility-based semantics, non-veridical
  attitudeBuilder := some (.doxastic .nonVeridical)

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
  -- Doxastic: accessibility-based semantics, non-veridical
  attitudeBuilder := some (.doxastic .nonVeridical)

/-- "want" — preferential attitude verb with infinitival complement -/
def want : VerbEntry where
  form := "want"
  form3sg := "wants"
  formPast := "wanted"
  formPastPart := "wanted"
  formPresPart := "wanting"
  complementType := .infinitival
  subjectTheta := some .experiencer
  controlType := .subjectControl
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential: degree-comparison positive → Class 3 (anti-rogative)
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- "hope" — preferential attitude verb (Class 3: anti-rogative) -/
def hope : VerbEntry where
  form := "hope"
  form3sg := "hopes"
  formPast := "hoped"
  formPastPart := "hoped"
  formPresPart := "hoping"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential: degree-comparison positive → C-distributive (PROVED) → Class 3
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- "expect" — preferential attitude verb (Class 3: anti-rogative) -/
def expect : VerbEntry where
  form := "expect"
  form3sg := "expects"
  formPast := "expected"
  formPastPart := "expected"
  formPresPart := "expecting"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential: degree-comparison positive → Class 3
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

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
  -- Preferential: degree-comparison positive → Class 3
  attitudeBuilder := some (.preferential (.degreeComparison .positive))

/-- "fear" — preferential attitude verb (Class 2: takes questions) -/
def fear : VerbEntry where
  form := "fear"
  form3sg := "fears"
  formPast := "feared"
  formPastPart := "feared"
  formPresPart := "fearing"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential: degree-comparison negative → C-distributive (PROVED) → Class 2
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

/-- "dread" — preferential attitude verb (Class 2: takes questions) -/
def dread : VerbEntry where
  form := "dread"
  form3sg := "dreads"
  formPast := "dreaded"
  formPastPart := "dreaded"
  formPresPart := "dreading"
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  verbClass := .attitude
  opaqueContext := true
  -- Preferential: degree-comparison negative → Class 2
  attitudeBuilder := some (.preferential (.degreeComparison .negative))

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
  -- Preferential: uncertainty-based → NOT C-distributive (PROVED) → Class 1
  attitudeBuilder := some (.preferential .uncertaintyBased)

/-- "seem" — raising verb (no theta role for subject) -/
def seem : VerbEntry where
  form := "seem"
  form3sg := "seems"
  formPast := "seemed"
  formPastPart := "seemed"
  formPresPart := "seeming"
  complementType := .infinitival
  subjectTheta := none  -- No theta role - raising
  controlType := .raising
  passivizable := false
  verbClass := .simple

/-- "cause" — necessity semantics (counterfactual dependence) -/
def cause : VerbEntry where
  form := "cause"
  form3sg := "causes"
  formPast := "caused"
  formPastPart := "caused"
  formPresPart := "causing"
  complementType := .infinitival  -- "X caused Y to VP"
  subjectTheta := some .agent     -- Causer (can also be event/stimulus)
  objectTheta := some .patient    -- Causee
  controlType := .objectControl   -- Y = agent of VP
  verbClass := .causative
  causativeBuilder := some .necessity
  -- Semantics: NadathurLauer2020.Necessity.causeSem

/-- "make" — sufficiency semantics (cause guaranteed effect) -/
def make : VerbEntry where
  form := "make"
  form3sg := "makes"
  formPast := "made"
  formPastPart := "made"
  formPresPart := "making"
  complementType := .smallClause  -- "X made Y VP" (bare infinitive)
  subjectTheta := some .agent     -- Causer
  objectTheta := some .patient    -- Causee
  controlType := .objectControl   -- Y = agent of VP
  verbClass := .causative
  causativeBuilder := some .sufficiency
  -- Semantics: NadathurLauer2020.Sufficiency.makeSem
  -- Coercive implication when VP is volitional

/-- "let" — permissive causative (related to "make" but weaker) -/
def let_ : VerbEntry where
  form := "let"
  form3sg := "lets"
  formPast := "let"
  formPastPart := "let"
  formPresPart := "letting"
  complementType := .smallClause  -- "X let Y VP"
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .sufficiency  -- Permissive = removing barrier (sufficiency)
  -- Note: "let" is an ENABLING causative, not FORCING
  -- See Wolff (2003) for force-dynamic analysis

/-- "have" — causative use (directive causation) -/
def have_causative : VerbEntry where
  form := "have"
  form3sg := "has"
  formPast := "had"
  formPastPart := "had"
  formPresPart := "having"
  complementType := .smallClause  -- "X had Y VP"
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .sufficiency
  -- "Have" implies social/authority-based causation

/-- "get" — causative use (persuasive causation) -/
def get_causative : VerbEntry where
  form := "get"
  form3sg := "gets"
  formPast := "got"
  formPastPart := "gotten"
  formPresPart := "getting"
  complementType := .infinitival  -- "X got Y to VP"
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .sufficiency
  -- "Get" implies persuasive/indirect causation

/-- "force" — coercive causative -/
def force : VerbEntry where
  form := "force"
  form3sg := "forces"
  formPast := "forced"
  formPastPart := "forced"
  formPresPart := "forcing"
  complementType := .infinitival  -- "X forced Y to VP"
  subjectTheta := some .agent
  objectTheta := some .patient
  controlType := .objectControl
  verbClass := .causative
  causativeBuilder := some .sufficiency
  -- "Force" lexically encodes coercion (unlike pragmatic "make")

/-- "devour" — transitive, no presupposition -/
def devour : VerbEntry where
  form := "devour"
  form3sg := "devours"
  formPast := "devoured"
  formPastPart := "devoured"
  formPresPart := "devouring"
  complementType := .np
  subjectTheta := some .agent
  objectTheta := some .patient
  verbClass := .simple

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
def claim : VerbEntry where
  form := "claim"
  form3sg := "claims"
  formPast := "claimed"
  formPastPart := "claimed"
  formPresPart := "claiming"
  verbClass := .communication
  complementType := .finiteClause

/-- "wonder" — embeds questions only -/
def wonder : VerbEntry where
  form := "wonder"
  form3sg := "wonders"
  formPast := "wondered"
  formPastPart := "wondered"
  formPresPart := "wondering"
  verbClass := .attitude
  complementType := .question
  takesQuestionBase := true
  opaqueContext := true

/-- "ask" — embeds questions -/
def ask : VerbEntry where
  form := "ask"
  form3sg := "asks"
  formPast := "asked"
  formPastPart := "asked"
  formPresPart := "asking"
  verbClass := .communication
  complementType := .question
  takesQuestionBase := true

/--
Get the CoS semantics for a verb (if it's a CoS verb).

Returns `some (cosSemantics t P)` if the verb has a CoS type,
where `P` is the activity predicate (complement denotation).
-/
def getCoSSemantics {W : Type*} (v : VerbEntry) (P : W → Bool) :
    Option (PrProp W) :=
  v.cosType.map λ t => cosSemantics t P

/--
Does this verb presuppose its complement?
-/
def presupposesComplement (v : VerbEntry) : Bool :=
  v.factivePresup || v.cosType.isSome

/--
Is this verb a presupposition trigger?
-/
def isPresupTrigger (v : VerbEntry) : Bool :=
  v.presupType.isSome

/--
Is this verb a causative?
-/
def isCausative (v : VerbEntry) : Bool :=
  v.verbClass == .causative

/-- Does this causative verb assert sufficiency (like "make")?

    DERIVED from the builder: a verb asserts sufficiency iff its builder
    uses `makeSem` as its semantic function (Nadathur & Lauer 2020, Def 23). -/
def assertsSufficiency (v : VerbEntry) : Bool :=
  v.causativeBuilder == some .sufficiency

/-- Does this causative verb assert necessity (like "cause")?

    DERIVED from the builder: a verb asserts necessity iff its builder
    uses `causeSem` as its semantic function (Nadathur & Lauer 2020, Def 24). -/
def assertsNecessity (v : VerbEntry) : Bool :=
  v.causativeBuilder == some .necessity

/--
Is this verb a preferential attitude predicate?
-/
def isPreferentialAttitude (v : VerbEntry) : Bool :=
  v.preferentialValence.isSome

-- Note: isAntiRogative and canEmbedQuestion are derived properties
-- defined in Theories/Montague/Verb/Attitude/BuilderProperties.lean

/-- "investigate" — rogative, embeds interrogatives only, no embedded inversion -/
def investigate : VerbEntry where
  form := "investigate"
  form3sg := "investigates"
  formPast := "investigated"
  formPastPart := "investigated"
  formPresPart := "investigating"
  verbClass := .simple
  complementType := .question
  subjectTheta := some .agent
  takesQuestionBase := true

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

/-- "remember" in factive/question-embedding sense:
    "I remember who left" / "*I remember [was Henry a communist↑]"
    Distinct from infinitival "remember to VP" (implicative). -/
def remember_q : VerbEntry where
  form := "remember"
  form3sg := "remembers"
  formPast := "remembered"
  formPastPart := "remembered"
  formPresPart := "remembering"
  verbClass := .factive
  complementType := .finiteClause
  subjectTheta := some .experiencer
  passivizable := false
  presupType := some .softTrigger
  factivePresup := true
  takesQuestionBase := true

/-- "forget" in factive/question-embedding sense:
    "I have forgotten [did Ann get A's↑]" (McCloskey 2006)
    Distinct from infinitival "forget to VP" (negative implicative). -/
def forget_q : VerbEntry where
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

/--
Get all verb entries as a list (for enumeration).
-/
def allVerbs : List VerbEntry := [
  -- Simple
  sleep, run, arrive, eat, kick, give, put, see, devour, read,
  -- Factive
  know, regret, realize, discover, notice,
  -- Change of State
  stop, quit, start, begin_, continue_, keep,
  -- Implicative / Control
  manage, fail, try_, persuade, promise, remember, forget,
  -- Doxastic Attitude
  believe, think,
  -- Preferential Attitude (Qing et al. 2025)
  want, hope, expect, wish,     -- Class 3: anti-rogative (positive, C-dist, TSP)
  fear, dread,                   -- Class 2: takes questions (negative, C-dist, no TSP)
  worry,                         -- Class 1: takes questions (non-C-distributive)
  -- Raising
  seem,
  -- Causative (Nadathur & Lauer 2020)
  cause,                         -- Necessity semantics
  make,                          -- Sufficiency semantics
  let_, have_causative, get_causative, force,  -- Other causatives
  -- Communication
  say, tell, claim,
  -- Question-embedding (Dayal 2025)
  wonder, ask, investigate, depend_on,
  -- Factive question-embedding senses
  remember_q, forget_q
]

-- Note: antiRogativeVerbs and questionEmbeddingVerbs are defined in
-- Theories/Montague/Verb/Attitude/BuilderProperties.lean (require derived properties)

/--
Look up a verb entry by citation form.
-/
def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (λ v => v.form == form)

/-- Map complement type to syntactic valence. -/
private def complementToValence : ComplementType → Valence
  | .none => .intransitive
  | .np => .transitive
  | .np_np => .ditransitive
  | _ => .transitive  -- Clause-embedding verbs are syntactically transitive

/--
Convert a verb entry to a `Word` (from Core.Basic) in 3sg present form.
-/
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

/--
Convert a verb entry to a `Word` in base/plural present form.
-/
def VerbEntry.toWordPl (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , number := some .pl
    }
  }

/--
Convert a verb entry to a `Word` in base/infinitive form.
-/
def VerbEntry.toWordBase (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .VERB
  , features := {
      valence := some (complementToValence v.complementType)
      , vform := some .infinitive
    }
  }

/-! ## Causative grounding theorems

These verify that the Fragment's causative annotations are consistent with
the formal semantics in `Theories.NadathurLauer2020`. -/

open Theories.NadathurLauer2020.Builder (CausativeBuilder)
open Theories.NadathurLauer2020.Sufficiency (makeSem)
open Theories.NadathurLauer2020.Necessity (causeSem)

/-- "make" uses sufficiency semantics: its truth conditions are
    computed by `makeSem`, not `causeSem`. -/
theorem make_semantics :
    make.causativeBuilder.map CausativeBuilder.toSemantics = some makeSem := rfl

/-- "cause" uses necessity semantics: its truth conditions are
    computed by `causeSem`, not `makeSem`. -/
theorem cause_semantics :
    cause.causativeBuilder.map CausativeBuilder.toSemantics = some causeSem := rfl

/-- "make" asserts sufficiency — derived from its builder. -/
theorem make_asserts_sufficiency : assertsSufficiency make = true := by native_decide

/-- "cause" asserts necessity — derived from its builder. -/
theorem cause_asserts_necessity : assertsNecessity cause = true := by native_decide

/-- "make" does NOT assert necessity. -/
theorem make_not_necessity : assertsNecessity make = false := by native_decide

/-- "cause" does NOT assert sufficiency. -/
theorem cause_not_sufficiency : assertsSufficiency cause = false := by native_decide

/-- All sufficiency-type verbs (make, let, have, get, force) share the same
    semantic function. -/
theorem sufficiency_verbs_share_semantics :
    make.causativeBuilder = let_.causativeBuilder ∧
    make.causativeBuilder = have_causative.causativeBuilder ∧
    make.causativeBuilder = get_causative.causativeBuilder ∧
    make.causativeBuilder = force.causativeBuilder := by
  constructor; · rfl
  constructor; · rfl
  constructor; · rfl
  · rfl

end Fragments.English.Predicates.Verbal
