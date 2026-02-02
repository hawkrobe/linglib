/-
# Verbal Predicate Lexicon Fragment

Lexical entries for verbal predicates, bundling everything needed to work with
a verb in semantic/pragmatic analysis:
- Surface form(s) and morphology
- Syntactic category/valence
- Argument structure (theta roles, control)
- Presupposition structure (if any)
- Link to compositional semantics

## Design

Each `VerbalPredicateEntry` provides the complete specification for a verbal predicate.
Downstream applications (RSA, NeoGricean, parsers) import this module
and get all the semantic machinery they need.

## Predicate Classes

1. **Simple** (sleep, run): No presupposition, standard denotation
2. **Factive** (know, regret): Presuppose complement truth
3. **Change-of-state** (stop, start): Presuppose prior state
4. **Implicative** (manage, fail): Entailment patterns
5. **Attitude** (believe, think, hope): Opaque contexts, preferential/doxastic semantics

## Usage

```lean
import Linglib.Fragments.English.Predicates.Verbal

-- Get the lexical entry for "stop"
#check Predicates.Verbal.stop
-- VerbalPredicateEntry with:
--   form = "stop"
--   predicateClass = .changeOfState
--   presupType = some .softTrigger
--   cosType = some .cessation
```
-/

import Linglib.Core.Basic
import Linglib.Core.Presupposition
import Linglib.Theories.Montague.Verb.ChangeOfState.Theory
import Linglib.Theories.Montague.Verb.Attitude.Doxastic
import Linglib.Theories.Montague.Verb.Attitude.Preferential
import Linglib.Theories.NadathurLauer2020.Basic

namespace Fragments.English.Predicates.Verbal

open Core.Presupposition
open Montague.Verb.ChangeOfState
open Montague.Verb.Attitude.Doxastic (Veridicality)
open Montague.Verb.Attitude.Preferential (AttitudeValence NVPClass PreferentialPredicate)

-- ============================================================================
-- Preferential Semantic Builders (Links to Montague)
-- ============================================================================

/--
Which Montague predicate builder this verb uses.

This links the Fragment entry to the compositional semantics in
`Montague.Verb.Attitude.Preferential`. Properties like C-distributivity
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

/--
C-distributivity is DERIVED from the semantic builder.

This is grounded in the Montague theorems:
- `degreeComparisonPredicate_isCDistributive` proves degree-comparison → C-dist
- `worry_not_cDistributive` proves uncertainty-based → NOT C-dist
-/
def PreferentialBuilder.isCDistributive : PreferentialBuilder → Bool
  | .degreeComparison _ => true   -- By degreeComparisonPredicate_isCDistributive
  | .uncertaintyBased => false    -- By worry_not_cDistributive
  | .relevanceBased _ => false    -- By analogous theorem

/-- Get the valence from the builder -/
def PreferentialBuilder.valence : PreferentialBuilder → AttitudeValence
  | .degreeComparison v => v
  | .uncertaintyBased => .negative  -- worry is negative
  | .relevanceBased v => v

/--
NVP class is DERIVED from C-distributivity and valence.

This matches `Preferential.classifyNVP` but computed from the builder.
-/
def PreferentialBuilder.nvpClass (b : PreferentialBuilder) : NVPClass :=
  if !b.isCDistributive then .class1_nonCDist
  else if b.valence == .negative then .class2_cDist_negative
  else .class3_cDist_positive

-- ============================================================================
-- Verb Classification
-- ============================================================================

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

/--
**Causative Type** (Nadathur & Lauer 2020)

Distinguishes causative verbs by their core semantic contribution:
- **Sufficiency**: "make" — cause was sufficient for effect (adding C guarantees E)
- **Necessity**: "cause" — cause was necessary for effect (counterfactual dependence)
- **Both**: "cause" with single cause — sufficient AND necessary

See `Theories.NadathurLauer2020` for the formal semantics.

| Type | Verb | Semantic Test |
|------|------|---------------|
| Sufficiency | make | Adding C to background → E happens |
| Necessity | cause | Removing C from background → E doesn't happen |

In overdetermination cases (multiple sufficient causes), "make" can be true
while "cause" is false (the cause wasn't necessary since another would have
produced the effect).
-/
inductive CausativeType where
  /-- Sufficiency semantics: cause guaranteed the effect (Definition 23) -/
  | sufficiency
  /-- Necessity semantics: effect depended on cause (Definition 24) -/
  | necessity
  deriving DecidableEq, Repr, BEq

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

-- ============================================================================
-- Verb Entry Structure
-- ============================================================================

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
  /-- For causative verbs: sufficiency (make) or necessity (cause)? -/
  causativeType : Option CausativeType := none

  -- === Intensionality ===
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false

  -- === Attitude-Specific Properties ===
  /-- For attitude verbs: veridicality (veridical = factive) -/
  attitudeVeridicality : Option Veridicality := none
  /-- Link to Montague preferential semantics (determines C-distributivity, NVP class) -/
  preferentialBuilder : Option PreferentialBuilder := none
  /-- For non-preferential question-embedding verbs (know, wonder, ask) -/
  takesQuestionBase : Bool := false

  deriving Repr, BEq

-- ============================================================================
-- Derived Properties (from Montague Semantics)
-- ============================================================================

/-- Valence is DERIVED from the preferential builder -/
def VerbEntry.preferentialValence (v : VerbEntry) : Option AttitudeValence :=
  v.preferentialBuilder.map (·.valence)

/-- C-distributivity is DERIVED from the preferential builder -/
def VerbEntry.cDistributive (v : VerbEntry) : Option Bool :=
  v.preferentialBuilder.map (·.isCDistributive)

/-- NVP class is DERIVED from the preferential builder -/
def VerbEntry.nvpClass (v : VerbEntry) : Option NVPClass :=
  v.preferentialBuilder.map (·.nvpClass)

/--
Can take questions: DERIVED for preferential verbs, base field for others.

For preferential verbs: determined by NVP class (Class 1, 2 can; Class 3 cannot)
For non-preferential verbs: uses `takesQuestionBase` field
-/
def VerbEntry.takesQuestion (v : VerbEntry) : Bool :=
  match v.nvpClass with
  | some .class1_nonCDist => true
  | some .class2_cDist_negative => true
  | some .class3_cDist_positive => false
  | none => v.takesQuestionBase

-- ============================================================================
-- Simple Verbs (No Presupposition)
-- ============================================================================

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

-- ============================================================================
-- Factive Verbs (Presuppose Complement Truth)
-- ============================================================================

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

-- ============================================================================
-- Change-of-State Verbs (Presuppose Prior State)
-- ============================================================================

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

-- ============================================================================
-- Implicative Verbs (Entailment Patterns)
-- ============================================================================

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

-- ============================================================================
-- Attitude Verbs (Opaque Contexts, No Factivity)
-- ============================================================================

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
  -- Doxastic properties (from Attitudes.Doxastic)
  attitudeVeridicality := some .nonVeridical

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
  -- Doxastic properties
  attitudeVeridicality := some .nonVeridical

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
  attitudeVeridicality := some .nonVeridical
  -- Link to Montague: degree-comparison positive → Class 3 (anti-rogative)
  preferentialBuilder := some (.degreeComparison .positive)

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
  attitudeVeridicality := some .nonVeridical
  -- Link to Montague: degree-comparison positive → C-distributive (PROVED) → Class 3
  preferentialBuilder := some (.degreeComparison .positive)

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
  attitudeVeridicality := some .nonVeridical
  preferentialBuilder := some (.degreeComparison .positive)

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
  attitudeVeridicality := some .nonVeridical
  preferentialBuilder := some (.degreeComparison .positive)

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
  attitudeVeridicality := some .nonVeridical
  -- Link to Montague: degree-comparison negative → C-distributive (PROVED) → Class 2
  preferentialBuilder := some (.degreeComparison .negative)

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
  attitudeVeridicality := some .nonVeridical
  preferentialBuilder := some (.degreeComparison .negative)

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
  attitudeVeridicality := some .nonVeridical
  -- Link to Montague: uncertainty-based → NOT C-distributive (PROVED) → Class 1
  preferentialBuilder := some .uncertaintyBased

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

-- ============================================================================
-- Causative Verbs (Nadathur & Lauer 2020)
-- ============================================================================

/-
Causative verbs assert causal relations between events:
- "cause" asserts **necessity**: the effect counterfactually depended on the cause
- "make" asserts **sufficiency**: the cause guaranteed the effect

See `Theories.NadathurLauer2020` for the formal semantics.

Key distinctions:
1. Overdetermination: "make" can be true while "cause" is false
   - "The lightning made the fire start" ✓ (sufficient)
   - "The lightning caused the fire" ✗ (not necessary; arsonist would have too)

2. Coercive implication: "make" + volitional action → coercion
   - "Kim made Sandy leave" implies Sandy didn't freely choose to leave
-/

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
  causativeType := some .necessity
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
  causativeType := some .sufficiency
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
  causativeType := some .sufficiency  -- Permissive = removing barrier (sufficiency)
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
  causativeType := some .sufficiency
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
  causativeType := some .sufficiency
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
  causativeType := some .sufficiency
  -- "Force" lexically encodes coercion (unlike pragmatic "make")

-- ============================================================================
-- Communication Verbs
-- ============================================================================

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

-- ============================================================================
-- Question-Embedding Verbs
-- ============================================================================

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

-- ============================================================================
-- Semantic Functions
-- ============================================================================

/--
Get the CoS semantics for a verb (if it's a CoS verb).

Returns `some (cosSemantics t P)` if the verb has a CoS type,
where `P` is the activity predicate (complement denotation).
-/
def getCoSSemantics {W : Type*} (v : VerbEntry) (P : W → Bool) :
    Option (PrProp W) :=
  v.cosType.map fun t => cosSemantics t P

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

/--
Does this causative verb assert sufficiency (like "make")?

Returns true for verbs where the cause guaranteed the effect.
-/
def assertsSufficiency (v : VerbEntry) : Bool :=
  v.causativeType == some .sufficiency

/--
Does this causative verb assert necessity (like "cause")?

Returns true for verbs where the effect counterfactually depended on the cause.
-/
def assertsNecessity (v : VerbEntry) : Bool :=
  v.causativeType == some .necessity

-- ============================================================================
-- NVP Properties (Qing et al. 2025)
-- ============================================================================

/--
Is this verb a preferential attitude predicate?
-/
def isPreferentialAttitude (v : VerbEntry) : Bool :=
  v.preferentialValence.isSome

/--
Is this verb anti-rogative (cannot take question complements canonically)?

Anti-rogative predicates are Class 3 NVPs: C-distributive + positive + TSP.
-/
def isAntiRogative (v : VerbEntry) : Bool :=
  match v.nvpClass with
  | some .class3_cDist_positive => true
  | _ => false

/--
Can this verb canonically embed a question?

Based on Qing et al. (2025) classification:
- Class 1 (non-C-distributive): Yes
- Class 2 (C-dist + negative): Yes
- Class 3 (C-dist + positive): No (anti-rogative)
- Non-preferential attitudes with takesQuestion: Yes
-/
def canEmbedQuestion (v : VerbEntry) : Bool :=
  match v.nvpClass with
  | some .class1_nonCDist => true
  | some .class2_cDist_negative => true
  | some .class3_cDist_positive => false
  | none => v.takesQuestion

/--
Get all verb entries as a list (for enumeration).
-/
def allVerbs : List VerbEntry := [
  -- Simple
  sleep, run, arrive, eat, kick, give, put, see,
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
  -- Question-embedding
  wonder, ask
]

/--
Get all anti-rogative verbs (Class 3 NVPs).
-/
def antiRogativeVerbs : List VerbEntry :=
  allVerbs.filter isAntiRogative

/--
Get all question-embedding verbs.
-/
def questionEmbeddingVerbs : List VerbEntry :=
  allVerbs.filter canEmbedQuestion

/--
Look up a verb entry by citation form.
-/
def lookup (form : String) : Option VerbEntry :=
  allVerbs.find? (fun v => v.form == form)

-- ============================================================================
-- Derived Syntactic Words
-- ============================================================================

/--
Convert a verb entry to a `Word` (from Core.Basic) in 3sg present form.
-/
def toWord3sg (v : VerbEntry) : Word :=
  { form := v.form3sg
  , cat := .V
  , features := {
      valence := some (match v.complementType with
        | .none => .intransitive
        | .np => .transitive
        | _ => .transitive)  -- Clause-embedding verbs are syntactically transitive
      , number := some .sg
      , person := some .third
      , voice := some .active
      , vform := some .finite
    }
  }

/--
Convert a verb entry to a `Word` in base/infinitive form.
-/
def toWordBase (v : VerbEntry) : Word :=
  { form := v.form
  , cat := .V
  , features := {
      valence := some (match v.complementType with
        | .none => .intransitive
        | _ => .transitive)
      , vform := some .infinitive
    }
  }

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Summary: Verb Lexicon Fragment

### VerbEntry Fields
- `form`, `form3sg`, `formPast`, `formPastPart`, `formPresPart`: Morphological forms
- `verbClass`: Semantic classification (simple, factive, CoS, implicative, attitude, causative)
- `complementType`: What complement the verb selects
- `presupType`: Presupposition trigger classification
- `cosType`: For CoS verbs, the change type (cessation/inception/continuation)
- `factivePresup`: Whether complement truth is presupposed
- `implicativeEntailment`: For implicatives, what is entailed
- `opaqueContext`: Whether the verb creates an opaque context
- `takesQuestion`: Whether the verb can embed questions
- `causativeType`: For causatives, sufficiency (make) or necessity (cause)

### Attitude-Specific Fields (Qing et al. 2025)
- `attitudeVeridicality`: Veridical (know) vs. non-veridical (believe)
- `preferentialValence`: Positive (hope) vs. negative (fear)
- `cDistributive`: Whether `x V Q` ⟺ `∃p ∈ Q. x V p`
- `nvpClass`: NVP classification (class1/class2/class3)

### Causative-Specific Fields (Nadathur & Lauer 2020)
- `causativeType`: `.sufficiency` (make) or `.necessity` (cause)
  - Sufficiency: adding cause guarantees effect
  - Necessity: removing cause blocks effect (counterfactual dependence)
  - In overdetermination, sufficiency ≠ necessity

### Key Functions
- `getCoSSemantics`: Get PrProp for CoS verbs
- `presupposesComplement`: Check if verb presupposes complement
- `isPresupTrigger`: Check if verb is a presupposition trigger
- `isPreferentialAttitude`: Check if verb is preferential
- `isAntiRogative`: Check if verb is anti-rogative (Class 3)
- `canEmbedQuestion`: Check if verb can embed questions
- `isCausative`: Check if verb is a causative
- `assertsSufficiency`: Check if causative asserts sufficiency
- `assertsNecessity`: Check if causative asserts necessity
- `lookup`: Find verb by citation form
- `toWord3sg`, `toWordBase`: Convert to syntactic Word

### Verb Inventory
**Simple**: sleep, run, eat, kick, give, put
**Factive**: know, regret, realize, discover, notice
**CoS**: stop, quit, start, begin, continue, keep
**Implicative**: manage, fail, remember, forget
**Doxastic Attitude**: believe, think
**Preferential Attitude (Class 3 - anti-rogative)**: want, hope, expect, wish
**Preferential Attitude (Class 2 - takes questions)**: fear, dread
**Preferential Attitude (Class 1 - non-C-dist)**: worry
**Raising**: seem
**Causative (Nadathur & Lauer 2020)**:
  - Necessity: cause
  - Sufficiency: make, let, have, get, force
**Communication**: say, tell, claim
**Question-embedding**: wonder, ask

### Causative Semantics (Nadathur & Lauer 2020)

The formal semantics for causatives are in `Theories.NadathurLauer2020`:
- `Sufficiency.makeSem`: ⟦X make Y⟧ = causallySufficient(dynamics, background, X, Y)
- `Necessity.causeSem`: ⟦X cause Y⟧ = causallyNecessary(dynamics, background, X, Y)

Key results:
1. Sufficiency ⇏ Necessity (overdetermination)
2. Necessity ⇏ Sufficiency (conjunctive causation)
3. "make" + volitional action → coercive implication
-/

end Fragments.English.Predicates.Verbal
